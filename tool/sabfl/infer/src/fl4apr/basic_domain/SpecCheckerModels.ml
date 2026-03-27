open! IStd
open! Vocab
module L = Logging
module Domain = SpecCheckerDomain
module Models = BasicDom.Models
module Val = SymDom.SymVal
module AbsVal = SymDom.AbsVal
module AbsTyp = SymDom.AbsTyp
module Node = InstrNode
module DiffVal = Domain.DiffVal
module SymDiff = Domain.SymDiff
module Loc = Domain.Loc

type exec =
     Domain.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> instantiate:
       (Domain.t -> Ident.t * Typ.t -> (Exp.t * Typ.t) list -> Procname.t -> Domain.t list option)
  -> callee:Procname.t
  -> (Exp.t * Typ.t) list
  -> (DiffVal.t * Domain.t) list

type is_model = Procname.t -> Typ.t list -> bool

let execute_equals ~is_exact ~instantiate ~arg_typs program astate node instr
    (expected_value, expected_diff) (actual_value, actual_diff) =
  let this_typ = Domain.read_typ_of_vals astate expected_value |> AbsTyp.typ_of in
  let this_typ =
    if Typ.is_pointer_to_void this_typ then List.hd_exn arg_typs |> snd |> strip_ptr else this_typ
  in
  L.d_printfln "try to find equals by %a" (Typ.pp_full (Pp.html Pp.Blue)) this_typ ;
  let results_v1_v2_diff =
    let ret_id = tmp_ret_id in
    match Program.find_equals_proc this_typ with
    | Some equals_proc -> (
      match instantiate astate (ret_id, Typ.int) arg_typs equals_proc with
      | Some results ->
          ( if Config.debug_mode then
            let Location.{file; line} = Program.pdesc_of program equals_proc |> Procdesc.get_loc in
            L.d_printfln "<a href=\"../../%s.html#LINE%d\">GO_TO_EQUALS</a>"
              (DB.source_file_encoding file) line ) ;
          List.map results ~f:(fun astate ->
              if Domain.is_exceptional astate then
                let symdiff_default =
                  if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty
                in
                (astate, AbsVal.top_primitive, AbsVal.top_primitive, symdiff_default)
              else
                let equals_value, equals_diff = Domain.eval astate node instr (Exp.Var ret_id) in
                L.d_printfln " - check is true? %a" DiffVal.pp (equals_value, equals_diff) ;
                (astate, AbsVal.singleton Domain.Val.one, equals_value, equals_diff) )
      | None ->
          [(astate, expected_value, actual_value, SymDiff.join expected_diff actual_diff)] )
    | None when is_exact ->
        [(astate, expected_value, actual_value, SymDiff.join expected_diff actual_diff)]
    | None ->
        [(astate, Domain.AbsVal.top_primitive, actual_value, SymDiff.join expected_diff actual_diff)]
  in
  List.map results_v1_v2_diff ~f:(fun (astate, v1, v2, symdiff) ->
      (Domain.remove_temps astate [Var.of_id tmp_ret_id], v1, v2, symdiff) )


module BuiltIn = struct
  let cast astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let arg_exp = List.hd_exn arg_typs |> fst in
    let diffval = Domain.eval astate node instr arg_exp in
    [(diffval, astate)]


  let instanceof astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    (* TODO: add type checking by using sizeof_exp and get_class_name_opt *)
    match List.unzip arg_typs |> fst with
    | [arg_exp; Exp.Sizeof {typ}] ->
        let arg_value, arg_diff = Domain.eval astate node instr arg_exp in
        let typ_of_instance = AbsTyp.make_instance typ in
        let true_states = Domain.prune_by_typ astate arg_value typ_of_instance ~is:true in
        let false_states = Domain.prune_by_typ astate arg_value typ_of_instance ~is:false in
        let true_value = (AbsVal.singleton (Domain.true_value astate instr_node), arg_diff) in
        let false_value = (AbsVal.singleton (Domain.false_value astate instr_node), arg_diff) in
        List.map true_states ~f:(fun astate -> (true_value, astate))
        @ List.map false_states ~f:(fun astate -> (false_value, astate))
    | [_; _] ->
        let symdiff = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
        let diffval = (AbsVal.top_primitive, symdiff) in
        (* This case happens in lambda function, TODO: refactoring *)
        [(diffval, astate)]
    | _ ->
        L.(die InternalError) "wrong invariant of instanceof"


  let instanceof astate node instr ~instantiate ~callee arg_typs =
    let instr_node = Node.of_pnode node instr in
    match Procdesc.Node.get_kind node with
    | Prune_node (_, _, PruneNodeKind_ExceptionHandler)
      when Domain.is_original astate
           && (not (Domain.has_dummy_ctx astate))
           && AbsBool.is_bottom (DynInfo.get_br_info Domain.(astate.current_ctxs) instr_node) ->
        [((AbsVal.singleton (Domain.false_value astate instr_node), SymDiff.empty), astate)]
    | _ ->
        instanceof astate node instr ~instantiate ~callee arg_typs


  let unwrap_exception astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let arg_exp, _ = List.hd_exn arg_typs in
    try
      let diffval = Domain.eval astate node instr arg_exp in
      [(diffval, Domain.unwrap_exception astate)]
    with Unexpected msg ->
      L.progress "[WARNING]: ==============@.%s@." msg ;
      []


  let get_array_length astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let arg_exp = List.hd_exn arg_typs |> fst in
    let arg_locs, args_diff = Domain.eval_lv astate node instr arg_exp in
    let index_locs = Domain.Loc.append_indexs arg_locs in
    let elements_value, elements_diff = Domain.read_locs astate (index_locs, args_diff) in
    if AbsVal.is_empty elements_value then [((AbsVal.singleton Val.zero, elements_diff), astate)]
    else [((AbsVal.top_primitive, elements_diff), astate)]
end

module Enum = struct
  let ordinal astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let this_exp, _ = List.hd_exn arg_typs in
    let _, symdiff = Domain.eval astate node instr this_exp in
    [((AbsVal.top_primitive, symdiff), astate)]
end

module Class = struct
  let cast astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] [_; (arg_exp, _)] = arg_typs in
    let diffval = Domain.eval astate node instr arg_exp in
    [(diffval, astate)]


  let newInstance astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = InstrNode.of_pnode node instr in
    let symdiff =
      let symdiff_default =
        if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty
      in
      List.fold arg_typs ~init:symdiff_default ~f:(fun acc (arg_exp, _) ->
          let _, symdiff = Domain.eval astate node instr arg_exp in
          SymDiff.join acc symdiff )
    in
    let instance_names =
      let classes_of_ctx = DynInfo.get_class_info Domain.(astate.current_ctxs) instr_node in
      if Typ.Name.Set.is_empty classes_of_ctx then
        DynInfo.get_class_info (DynInfo.all_ctxs ()) instr_node
      else classes_of_ctx
    in
    let abstyp =
      match Typ.Name.Set.is_singleton_or_more instance_names with
      | Singleton name ->
          AbsTyp.make_exact (Typ.mk_struct name)
      | _ ->
          AbsTyp.make_instance (Typ.mk_struct Typ.Name.Java.java_lang_object)
    in
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    [((AbsVal.singleton value, symdiff), astate)]
end

module Collection = struct
  let abstyp = AbsTyp.make_instance Fl4aprModels.Collection.typ

  let setIsEmpty node instr (locs, symdiff) astate =
    let instr_node = Node.of_pnode node instr in
    let is_empty_field_loc = Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) locs in
    let elements_field_loc = Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mElementsField) locs in
    Domain.store_locs instr_node elements_field_loc (AbsVal.empty, symdiff) astate
    |> Domain.store_locs instr_node is_empty_field_loc (AbsVal.singleton Val.one, symdiff)


  let get_is_empty (this_locs, this_diff) astate =
    let is_empty_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) this_locs
    in
    Domain.read_locs astate (is_empty_field_locs, this_diff)


  let get_elements (this_locs, this_diff) astate =
    let elements_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mElementsField) this_locs
    in
    Domain.read_locs astate (elements_field_locs, this_diff)


  let get_field_values this_locs_diff astate =
    (get_is_empty this_locs_diff astate, get_elements this_locs_diff astate)


  let store_is_empty node instr this_locs_diff is_empty_valdiff astate =
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = this_locs_diff in
    let is_empty_value, is_empty_diff = is_empty_valdiff in
    let is_empty_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) this_locs
    in
    let symdiff = SymDiff.join this_diff is_empty_diff in
    Domain.store_locs instr_node is_empty_field_locs (is_empty_value, symdiff) astate


  let store_elements node instr (this_locs, this_diff) (elements_value, elements_diff) astate =
    let instr_node = Node.of_pnode node instr in
    let elements_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mElementsField) this_locs
    in
    let symdiff = SymDiff.join this_diff elements_diff in
    Domain.store_locs instr_node elements_field_locs (elements_value, symdiff) astate


  let add_to_new_collection node instr ~this_locs_diff ~value astate =
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = this_locs_diff in
    let add_value, add_diff = value in
    let is_empty_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) this_locs
    in
    let elements_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mElementsField) this_locs
    in
    let elements_value, elements_diff = Domain.read_locs astate (elements_field_locs, this_diff) in
    let symdiff = SymDiff.join elements_diff add_diff in
    let astate =
      (* value of is_empty is always zero regardless of elements *)
      Domain.store_locs instr_node elements_field_locs
        (AbsVal.join elements_value add_value, symdiff)
        astate
      |> Domain.store_locs instr_node is_empty_field_locs (AbsVal.singleton Val.zero, this_diff)
    in
    (astate, symdiff)


  let add_to_collection node instr ~this_exp ~value astate =
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    add_to_new_collection node instr ~this_locs_diff ~value astate


  let enumeration_of astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let diffval = Domain.eval astate node instr this_exp in
    [(diffval, astate)]


  let emptyCollection astate node instr ~instantiate:_ ~callee:_ _ =
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    let value = AbsVal.singleton value in
    let symdiff = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let astate = setIsEmpty node instr (Domain.Loc.from_vals value, symdiff) astate in
    let diffval = (value, symdiff) in
    [(diffval, astate)]


  let newEmptyCollection astate node instr ~instantiate:_ ~callee:_ _ =
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    let value = AbsVal.singleton value in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let new_locs_diff = (Domain.Loc.from_vals value, symdiff_default) in
    let diffval = (value, symdiff_default) in
    let astate = setIsEmpty node instr new_locs_diff astate in
    [(diffval, astate)]


  let newCollectionFromCol astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    let value = AbsVal.singleton value in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let new_locs_diff = (Domain.Loc.from_vals value, symdiff_default) in
    let diffval = (value, symdiff_default) in
    let[@warning "-8"] [(arg_exp, _)] = arg_typs in
    let arg_locs = Domain.eval_lv astate node instr arg_exp in
    let is_empty_diffval, elements_diffval = get_field_values arg_locs astate in
    let astate =
      store_is_empty node instr new_locs_diff is_empty_diffval astate
      |> store_elements node instr new_locs_diff elements_diffval
    in
    [(diffval, astate)]


  let newCollectionFromArray astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    let value = AbsVal.singleton value in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let new_locs_diff = (Domain.Loc.from_vals value, symdiff_default) in
    let diffval = (value, symdiff_default) in
    let[@warning "-8"] [(arg_exp, _)] = arg_typs in
    let arg_locs = Domain.eval_lv astate node instr arg_exp in
    let elements_diffval =
      Domain.read_locs astate (Loc.append_indexs (fst arg_locs), snd arg_locs)
    in
    let is_empty_diffval =
      (* TODO: could spcifiy detailed value *) (AbsVal.top_primitive, symdiff_default)
    in
    let astate =
      store_is_empty node instr new_locs_diff is_empty_diffval astate
      |> store_elements node instr new_locs_diff elements_diffval
    in
    [(diffval, astate)]


  let init astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let loc, symdiff = Domain.eval_lv astate node instr this_exp in
    [(DiffVal.empty, setIsEmpty node instr (loc, symdiff) astate)]


  let initFromCol astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let arg_locs = Domain.eval_lv astate node instr arg_exp in
    let is_empty_diffval, elements_diffval = get_field_values arg_locs astate in
    let astate =
      store_is_empty node instr this_locs_diff is_empty_diffval astate
      |> store_elements node instr this_locs_diff elements_diffval
    in
    [(DiffVal.empty, astate)]


  let isEmpty astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, symdiff = Domain.eval_lv astate node instr this_exp in
    let is_empty_field_locs =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) this_locs
    in
    let diffval = Domain.read_locs astate (is_empty_field_locs, symdiff) in
    [(diffval, astate)]


  let iterator astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let instr_node = Node.of_pnode node instr in
    let iter_typ = Fl4aprModels.Collection.iterator_typ in
    let astate, iterator =
      Domain.make_allocsite astate instr_node ~abstyp:(AbsTyp.make_instance iter_typ)
    in
    let iterator_locs = Domain.Loc.from_vals (Domain.AbsVal.singleton iterator) in
    let is_empty_diffval, elements_diffval = get_field_values (this_locs, this_diff) astate in
    let astate =
      store_is_empty node instr (iterator_locs, this_diff) is_empty_diffval astate
      |> store_elements node instr (iterator_locs, this_diff) elements_diffval
    in
    [((AbsVal.singleton iterator, this_diff), astate)]


  let hasNext astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, symdiff = Domain.eval_lv astate node instr this_exp in
    let is_empty_field_loc =
      Domain.Loc.Set.map (Domain.Loc.append_field ~fn:mIsEmptyField) this_locs
    in
    let is_empty_value, symdiff = Domain.read_locs astate (is_empty_field_loc, symdiff) in
    (* TODO: check is_empty_value *)
    let diffval = (Domain.make_injective ~f:Models.neg [is_empty_value], symdiff) in
    [(diffval, astate)]


  let add astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] this_exp, arg_exp =
      match arg_typs with
      | [(this_exp, _); (arg_exp, _)] ->
          (this_exp, arg_exp)
      | [(this_exp, _); _; (arg_exp, _)] ->
          (this_exp, arg_exp)
    in
    let value = Domain.eval astate node instr arg_exp in
    let astate, symdiff = add_to_collection node instr ~this_exp ~value astate in
    [((AbsVal.top_primitive, symdiff), astate)]


  let addAll astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] this_exp, arg_exp =
      match arg_typs with
      | [(this_exp, _); (arg_exp, _)] ->
          (this_exp, arg_exp)
      | [(this_exp, _); _; (arg_exp, _)] ->
          (this_exp, arg_exp)
    in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let arg_locs, arg_diff = Domain.eval_lv astate node instr arg_exp in
    let is_empty_arg_diffval, elements_arg_diffval = get_field_values (arg_locs, arg_diff) astate in
    let is_empty_org_diffval, elements_org_diffval =
      get_field_values (this_locs, this_diff) astate
    in
    let is_empty_diffval =
      let joined = DiffVal.join is_empty_org_diffval is_empty_arg_diffval in
      let is_nonempty diffval = AbsVal.equal (AbsVal.singleton Val.one) (fst diffval) in
      if is_nonempty is_empty_org_diffval || is_nonempty is_empty_arg_diffval then
        (AbsVal.singleton Val.one, snd joined)
      else DiffVal.join is_empty_org_diffval is_empty_arg_diffval
    in
    let elements_diffval = DiffVal.join elements_org_diffval elements_arg_diffval in
    let astate = store_is_empty node instr (this_locs, this_diff) is_empty_diffval astate in
    let astate = store_elements node instr (this_locs, this_diff) elements_diffval astate in
    [((AbsVal.top_primitive, snd elements_diffval), astate)]


  let next astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    (* FIXME: currently, next always return next value other than NoSuchElement Exception *)
    let _, (elements_value, symdiff) = get_field_values (this_locs, this_diff) astate in
    let astate_empty =
      store_is_empty node instr (this_locs, this_diff) (AbsVal.singleton Val.one, symdiff) astate
      |> store_elements node instr (this_locs, this_diff) (AbsVal.bottom, symdiff)
    in
    let astate_non_empty =
      store_is_empty node instr (this_locs, this_diff) (AbsVal.singleton Val.zero, symdiff) astate
    in
    [((elements_value, symdiff), astate_empty); ((elements_value, symdiff), astate_non_empty)]


  let get astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* ignore index, return whole elements *)
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let elements_diffval = get_elements (this_locs, this_diff) astate in
    [(elements_diffval, astate)]


  let remove astate node instr ~instantiate:_ ~callee arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let elements_value, elements_diff = get_elements (this_locs, this_diff) astate in
    let[@warning "-8"] symdiff =
      match arg_typs with
      | [_] ->
          (* AbstractQueue.remove() *)
          elements_diff
      | _ :: (index_exp, _) :: _ ->
          let _, index_diff = Domain.eval astate node instr index_exp in
          SymDiff.join index_diff elements_diff
    in
    let retval = (AbsVal.top_primitive, symdiff) in
    let exn_state =
      let abstyp =
        "java.lang.UnsupportedOperationException" |> AbsTyp.typ_from_string |> AbsTyp.make_exact
      in
      if
        Domain.is_dynamic_throw astate instr_node |> is_no
        && SymDiff.is_diff this_diff
        && Domain.(Changed.is_empty astate.changed)
      then (
        let pdesc = Program.pdesc_of (Program.from_marshal ()) Domain.(astate.current_proc) in
        let ret_var = Procdesc.get_ret_var pdesc in
        L.d_printfln "New exception is thrown by patch" ;
        [(retval, Domain.bind_exn_extern_absval instr_node ret_var ~abstyp callee [retval] astate)]
        )
      else []
    in
    let astate =
      store_elements node instr (this_locs, this_diff) (elements_value, symdiff) astate
      |> store_is_empty node instr (this_locs, this_diff) (AbsVal.top_primitive, symdiff)
    in
    [(retval, astate)] @ exn_state


  let contains astate node instr ~instantiate ~callee:_ arg_typs =
    let program = Program.from_marshal () in
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, arg_typ) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let elements_value, elements_diff = get_elements (this_locs, this_diff) astate in
    let elt_value, elt_diff = Domain.eval astate node instr arg_exp in
    let symdiff = SymDiff.join elements_diff elt_diff in
    if AbsVal.is_empty elements_value then [((AbsVal.singleton Val.zero, symdiff), astate)]
    else
      let arg_typs = [(arg_exp, arg_typ); (Exp.Var tmp_arg_id, arg_typ)] in
      let astate = Domain.store_reg tmp_arg_id (elements_value, elements_diff) astate in
      (* TODO: should split true and false state with equality condition *)
      let results_v1_v2_diff =
        execute_equals ~is_exact:true ~instantiate ~arg_typs program astate node instr
          (elt_value, elt_diff) (elements_value, elements_diff)
      in
      List.concat_map results_v1_v2_diff ~f:(fun (astate, v1, v2, symdiff) ->
          let astate = Domain.remove_temps astate [Var.of_id tmp_arg_id] in
          let true_val =
            if
              AbsVal.exists
                (fun arg_val -> AbsVal.exists (Domain.is_equal_sat astate arg_val) v2)
                v1
            then AbsVal.singleton Val.one
            else AbsVal.bottom
          in
          let false_val =
            if AbsVal.is_empty v1 then AbsVal.singleton Val.zero
            else if
              AbsVal.exists
                (fun arg_val -> AbsVal.exists (Domain.is_inequal_sat astate arg_val) v2)
                v1
            then AbsVal.singleton Val.zero
            else AbsVal.bottom
          in
          [((AbsVal.join true_val false_val, symdiff), astate)] )


  let toArray astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let elements_value, symdiff = get_elements (this_locs, this_diff) astate in
    let elt_typ = Domain.read_typ_of_vals astate elements_value in
    let array_typ = AbsTyp.mk_array elt_typ in
    let astate, new_array_value = Domain.make_allocsite astate ~abstyp:array_typ instr_node in
    let array_loc = Domain.Loc.of_heap new_array_value in
    let array_index_loc = Domain.Loc.append_index ~index:Val.top_primitive array_loc in
    (* this.elements -> elements
       ret -> new_l
       new_l[*] -> elements *)
    let astate = Domain.store_loc instr_node array_index_loc (elements_value, symdiff) astate in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    [((AbsVal.singleton new_array_value, symdiff_default), astate)]


  let _of astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let astate, value = Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp in
    let value = AbsVal.singleton value in
    let elements_diffval =
      List.fold arg_typs ~init:DiffVal.empty ~f:(fun acc (arg_exp, _) ->
          Domain.eval astate node instr arg_exp |> DiffVal.join acc )
    in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let new_locs_diff = (Domain.Loc.from_vals value, symdiff_default) in
    let astate, _ =
      add_to_new_collection node instr ~this_locs_diff:new_locs_diff ~value:elements_diffval astate
    in
    [((value, symdiff_default), astate)]


  let copyOf astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let astate, value = Domain.make_allocsite astate instr_node ~abstyp in
    let arg_exp, arg_typ = List.hd_exn arg_typs in
    let value = AbsVal.singleton value in
    let elements_diffval =
      let arg_locs, args_diff = Domain.eval_lv astate node instr arg_exp in
      if Fl4aprModels.is_collection_arg arg_typ then get_elements (arg_locs, args_diff) astate
      else Domain.read_locs astate (Domain.Loc.append_indexs arg_locs, args_diff)
    in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let new_locs_diff = (Domain.Loc.from_vals value, symdiff_default) in
    let astate, _ =
      add_to_new_collection node instr ~this_locs_diff:new_locs_diff ~value:elements_diffval astate
    in
    [((value, symdiff_default), astate)]
end

module System = struct
  let currentTimeMillis astate node instr ~instantiate:_ ~callee _ =
    let instr_node = Node.of_pnode node instr in
    let value = Domain.make_fresh astate ~f:callee ~typ:Typ.int instr_node in
    let symdiff = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    [((AbsVal.singleton value, symdiff), astate)]


  let arraycopy astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] [(src_exp, _); _; (dest_exp, _); _; _] = arg_typs in
    let src_locs, src_diff = Domain.eval_lv astate node instr src_exp in
    let dest_locs, dest_diff = Domain.eval_lv astate node instr dest_exp in
    let elements_value, elements_diff =
      Domain.read_locs astate (Loc.append_indexs src_locs, src_diff)
    in
    let symdiff = SymDiff.join dest_diff elements_diff in
    let astate =
      Domain.store_locs instr_node (Loc.append_indexs dest_locs) (elements_value, symdiff) astate
    in
    [(DiffVal.empty, astate)]
end

(*
     TODO: modeling static field load & read_field & init
     module Primitives = struct
     let mValue = Fieldname.make (Typ.Name.Java.from_string "Primitive") "mValue"

     let classes = ["java.lang.Boolean"]

     let booleanValue 
       let is_model callee arg_typs  =
         match (callee, arg_typs) with
         | Procname.Java mthd, Sil.Call (_, _, [(_, _)], _, _)
           when String.equal (Procname.get_method callee) "booleanValue" ->
             implements classes (Procname.Java.get_class_type_name mthd)
         | _ ->
             false
       in
       astate node instr ~instantiate:_ ~callee:(_) arg_typs  =
         let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
         let value =
           match Domain.eval astate node instr this_exp with
           | Val.VHeap (Symbol s) ->
               let deref_field = SymDom.Symbol.to_ap s |> AccessExpr.get_deref_field in
               if String.equal deref_field "FALSE" then Domain.Val.zero
               else if String.equal deref_field "TRUE" then Domain.Val.one
               else Val.make_extern (Node.of_pnode node instr) Typ.int
           | _ ->
               Val.make_extern (Node.of_pnode node instr) Typ.int
         in
         [Domain.store_reg ~should_update astate ret_id value]
       in
       (is_model, exec)


     let models = [booleanValue]
   end *)

module Lang = struct
  let valueField = Fieldname.make (Typ.Name.Java.from_string "java.lang.StringBuilder") "value"

  let eval_str astate node instr str_exp =
    let str_value, str_diff = Domain.eval astate node instr str_exp in
    let field_locs = Domain.Loc.append_fields ~fn:valueField (Domain.Loc.from_vals str_value) in
    Domain.read_locs astate (field_locs, str_diff)


  let init
      (* TODO: currently, we assume argument is constant string *)
      (* TODO: init for StringBuilder *)
        astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let str_value, str_diff = eval_str astate node instr str_exp in
    let symdiff = SymDiff.join this_diff str_diff in
    let value_field_loc = Domain.Loc.append_fields ~fn:valueField this_locs in
    [(DiffVal.empty, Domain.store_locs instr_node value_field_loc (str_value, symdiff) astate)]


  let init_default astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let str_value, _ = eval_str astate node instr (Exp.Const (Cstr "")) in
    let value_field_loc = Domain.Loc.append_fields ~fn:valueField this_locs in
    [(DiffVal.empty, Domain.store_locs instr_node value_field_loc (str_value, this_diff) astate)]


  let init_size astate node instr ~instantiate:_ ~callee arg_typs =
    (* new StringBuilder (size) *)
    let[@warning "-8"] ((this_exp, _) :: (size_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let program = Program.from_marshal () in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let size_value, size_diff = Domain.eval astate node instr size_exp in
    let ret_var = Procdesc.get_ret_var (Domain.(astate.current_proc) |> Program.pdesc_of program) in
    let symdiff = SymDiff.join this_diff size_diff in
    let is_dynamic_throw = Domain.is_dynamic_throw astate instr_node in
    let is_dynamic_normal = Domain.is_dynamic_normal astate instr_node in
    let exn_states =
      Domain.bind_exn_extern_absval instr_node ret_var ~abstyp:AbsTyp.exn_typ callee
        [(size_value, size_diff)]
        astate
      |> Domain.prune_by_binop instr_node ~is_org_flow:is_dynamic_throw Binop.Lt size_value
           (AbsVal.singleton Val.zero) size_diff
    in
    let normal_states =
      let str_value, _ = eval_str astate node instr (Exp.Const (Cstr "")) in
      let value_field_loc = Domain.Loc.append_fields ~fn:valueField this_locs in
      Domain.store_locs instr_node value_field_loc (str_value, this_diff) astate
      |> Domain.prune_by_binop instr_node ~is_org_flow:is_dynamic_normal Binop.Ge size_value
           (AbsVal.singleton Val.zero) symdiff
    in
    List.map ~f:(fun s -> (DiffVal.empty, s)) (exn_states @ normal_states)


  let format astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let symdiff =
      List.fold arg_typs ~init:SymDiff.empty ~f:(fun acc (arg_exp, _) ->
          let _, arg_diff = eval_str astate node instr arg_exp in
          SymDiff.join arg_diff acc )
    in
    [((AbsVal.top_primitive, symdiff), astate)]


  let isEmpty astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_value, this_diff = eval_str astate node instr this_exp in
    match AbsVal.is_singleton_or_more this_value with
    | Singleton (VString "") ->
        [((AbsVal.singleton Val.one, this_diff), astate)]
    | Singleton (VString _) ->
        [((AbsVal.singleton Val.zero, this_diff), astate)]
    | _ ->
        let empty_states =
          Domain.prune_by_binop ~is_org_flow:`Unknown instr_node Binop.Eq this_value
            (Val.VString "" |> AbsVal.singleton)
            this_diff astate
          |> List.map ~f:(fun s -> ((AbsVal.singleton Val.one, this_diff), s))
        in
        let non_empty_states =
          Domain.prune_by_binop ~is_org_flow:`Unknown instr_node Binop.Ne this_value
            (Val.VString "" |> AbsVal.singleton)
            this_diff astate
          |> List.map ~f:(fun s -> ((AbsVal.singleton Val.zero, this_diff), s))
        in
        empty_states @ non_empty_states


  let length astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_value, this_diff = eval_str astate node instr this_exp in
    match AbsVal.is_singleton_or_more this_value with
    | Singleton (Val.VString str) ->
        let length_value = Val.make_int (IntLit.of_int (String.length str)) in
        [((AbsVal.singleton length_value, this_diff), astate)]
    | _ ->
        [((AbsVal.top_primitive, this_diff), astate)]


  let normalize : Domain.Val.t -> Domain.Val.t = function
    | VTopPrimitive ->
        Domain.Val.make_string ".*"
    | v ->
        Domain.Val.normalize v


  let append astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* StringBuilder.append(String) 
     * StringWriter.append(String, _, _) *)
    let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
    let instr_node = Node.of_pnode node instr in
    let this_locs, _ = Domain.eval_lv astate node instr this_exp in
    let field_locs = Domain.Loc.append_fields this_locs ~fn:valueField in
    let this_value, _ = Domain.eval astate node instr this_exp in
    let this_str, this_diff = eval_str astate node instr this_exp in
    let str_value, str_diff = eval_str astate node instr str_exp in
    let str_to_append =
      if AbsVal.for_all (not <<< Domain.is_inequal_sat astate Domain.Val.null) str_value then
        AbsVal.set_add (Domain.Val.make_string "null") str_value
      else str_value
    in
    let symdiff = SymDiff.join this_diff str_diff in
    let astate =
      AbsVal.fold
        (fun this_str astate ->
          AbsVal.fold
            (fun str_to_append astate ->
              let appended_value =
                match (normalize this_str, normalize str_to_append) with
                | Val.VString str1, Val.VString str2
                  when String.equal ".*" str1 && String.equal ".*" str2 ->
                    AbsVal.top_primitive
                | Val.VString str1, Val.VString str2 ->
                    Domain.Val.make_string (String.concat [str1; str2]) |> AbsVal.singleton
                | this_str, str_to_append ->
                    Domain.make_injective ~f:Models.append
                      [AbsVal.singleton this_str; AbsVal.singleton str_to_append]
              in
              Domain.store_locs instr_node field_locs (appended_value, symdiff) astate )
            str_to_append astate )
        this_str astate
    in
    [((this_value, this_diff), astate)]


  let toString astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* StringBuilder.toString(this) *)
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_value, this_diff = eval_str astate node instr this_exp in
    [((this_value, this_diff), astate)]


  let contains astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* StringBuilder.contains(this, str) *)
    let[@warning "-8"] ((this_exp, _) :: (str_exp, _) :: _) = arg_typs in
    let _, this_diff = eval_str astate node instr this_exp in
    let _, str_diff = eval_str astate node instr str_exp in
    let symdiff = SymDiff.join this_diff str_diff in
    [((AbsVal.top_primitive, symdiff), astate)]
end

module Writer = struct
  let fn = Fl4aprModels.Writer.field

  let str = AbsVal.top_primitive

  let store_string astate instr_node this_locs this_diff =
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    Domain.store_locs instr_node field_locs (str, this_diff) astate


  let to_string astate this_locs this_diff =
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let _, str_diff = Domain.read_locs astate (field_locs, this_diff) in
    (str, str_diff)


  let append_string astate instr_node this_locs this_diff =
    let _, str_diff = to_string astate this_locs this_diff in
    store_string astate instr_node this_locs str_diff


  let init astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    [(DiffVal.empty, store_string astate instr_node this_locs this_diff)]


  let append astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: other_args) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let symdiff =
      List.fold other_args ~init:this_diff ~f:(fun acc (arg_exp, _) ->
          let _, diff = Domain.eval astate node instr arg_exp in
          SymDiff.join diff acc )
    in
    [(Domain.eval astate node instr this_exp, append_string astate instr_node this_locs symdiff)]


  let write = append

  let toString astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let values = Domain.read_locs astate (field_locs, this_diff) in
    [(values, astate)]
end

module PrintWriter = struct
  let fn = Fl4aprModels.PrintWriter.field

  let init_new astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    (* this.out -> allocsite *)
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let abstyp = AbsTyp.make_instance Fl4aprModels.Writer.typ in
    let astate, allocsite = Domain.make_allocsite astate ~abstyp instr_node in
    let astate =
      Domain.store_locs instr_node field_locs (AbsVal.singleton allocsite, this_diff) astate
    in
    (* allocsite.buf -> Top *)
    [ ( DiffVal.empty
      , Writer.store_string astate instr_node (Loc.Set.singleton (Loc.of_heap allocsite)) this_diff
      ) ]


  let init_arg astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    (* this.out -> arg_val *)
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let arg_val, arg_diff = Domain.eval astate node instr arg_exp in
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let diff = SymDiff.join this_diff arg_diff in
    [(DiffVal.empty, Domain.store_locs instr_node field_locs (arg_val, diff) astate)]


  let append astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: other_args) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let writer_val, writer_diff = Domain.read_locs astate (field_locs, this_diff) in
    (* this.out -> writer *)
    let symdiff =
      List.fold other_args ~init:writer_diff ~f:(fun acc (arg_exp, _) ->
          let _, diff = Domain.eval astate node instr arg_exp in
          SymDiff.join diff acc )
    in
    [ ( Domain.eval astate node instr this_exp
      , Writer.append_string astate instr_node (Loc.from_vals writer_val) symdiff ) ]


  let write = append

  let println = append

  let toString astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Domain.Loc.append_fields ~fn this_locs in
    let writer_val, writer_diff = Domain.read_locs astate (field_locs, this_diff) in
    [(Writer.to_string astate (Loc.from_vals writer_val) writer_diff, astate)]
end

module Assert = struct
  let assertEquals astate node instr ~instantiate ~callee:_ arg_typs =
    let program = Program.from_marshal () in
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] (e1, typ1), (e2, typ2), is_exact =
      match arg_typs with
      | [expected; actual] ->
          (expected, actual, true)
      | [(_, typ); expected; actual] when Typ.is_pointer typ ->
          (expected, actual, true)
      | [expected; actual; (Exp.Const (Cfloat 0.0), _)] ->
          (expected, actual, true)
      | [expected; actual; _] ->
          (expected, actual, false)
      | [(_, _); expected; actual; (Exp.Const (Cfloat 0.0), _)] ->
          (* double equality with delta *)
          (expected, actual, true)
      | [(_, _); expected; actual; _] ->
          (expected, actual, false)
    in
    let expected_value, expected_diff = Domain.eval astate node instr e1 in
    let actual_value, actual_diff = Domain.eval astate node instr e2 in
    execute_equals ~is_exact ~instantiate
      ~arg_typs:[(e1, typ1); (e2, typ2)]
      program astate node instr (expected_value, expected_diff) (actual_value, actual_diff)
    |> List.concat_map ~f:(fun (astate, v1, v2, symdiff) ->
           Domain.exec_assertion instr_node Binop.Eq v1 v2 symdiff astate
           |> List.map ~f:(fun astate -> (DiffVal.empty, astate)) )


  let assertSame (* assertArrayEquals not supported *) astate node instr ~instantiate:_ ~callee
      arg_typs =
    let instr_node = InstrNode.of_pnode node instr in
    let[@warning "-8"] e1, e2 =
      match arg_typs with
      | [(expected, _); (actual, _)] ->
          (expected, actual)
      | [(_, _); (expected, _); (actual, _)] ->
          (expected, actual)
    in
    let expected_value, expected_diff = Domain.eval astate node instr e1 in
    let actual_value, actual_diff = Domain.eval astate node instr e2 in
    let symdiff = SymDiff.join expected_diff actual_diff in
    let binop =
      let method_name = Procname.get_method callee in
      if String.equal "assertSame" method_name then Binop.Eq
      else if String.equal "assertNotSame" method_name then Binop.Ne
      else L.(die InternalError) "Invalid method name"
    in
    Domain.exec_assertion instr_node binop expected_value actual_value symdiff astate
    |> List.map ~f:(fun s -> (DiffVal.empty, s))


  let assertEqualsConst (* assertArrayEquals not supported *) astate node instr ~instantiate:_
      ~callee arg_typs =
    let instr_node = InstrNode.of_pnode node instr in
    let method_name = Procname.get_method callee in
    let[@warning "-8"] exp =
      match arg_typs with [(actual, _)] -> actual | [(_, _); (actual, _)] -> actual
    in
    let[@warning "-8"] const =
      match method_name with
      | "assertTrue" ->
          Domain.Val.one
      | "assertFalse" ->
          Domain.Val.zero
      | "assertNull" ->
          Domain.Val.null
      | "assertNotNull" ->
          Domain.Val.null
    in
    let actual_value, actual_diff = Domain.eval astate node instr exp in
    let binop = if String.equal "assertNotNull" method_name then Binop.Ne else Binop.Eq in
    Domain.exec_assertion instr_node binop (AbsVal.singleton const) actual_value actual_diff astate
    |> List.map ~f:(fun s -> (DiffVal.empty, s))


  let fail astate node instr ~instantiate:_ ~callee:_ _ =
    L.d_printfln "the state is invalidated because of fail" ;
    let instr_node = InstrNode.of_pnode node instr in
    let ret_var =
      Program.pdesc_of (Program.from_marshal ()) Domain.(astate.current_proc)
      |> Procdesc.get_ret_var
    in
    [ ( DiffVal.empty
      , Domain.throw_exn instr_node ret_var ~exn_typ_str:"org.junit.Assert.AssertionError" astate )
    ]
end

module EventListenerList = struct
  let mListenerListField =
    Fieldname.make (Typ.Name.Java.from_string "javax.swing.event.EventListenerList") "mListenerList"


  let init astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = InstrNode.of_pnode node instr in
    let this_locs, symdiff = Domain.eval_lv astate node instr this_exp in
    let listenerList_field_locs = Domain.Loc.append_fields this_locs ~fn:mListenerListField in
    (* this -> this_locs, this_locs.listenerList -> {} *)
    [ ( DiffVal.empty
      , Domain.store_locs instr_node listenerList_field_locs (AbsVal.empty, symdiff) astate ) ]


  let add astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: (_, _) :: (arg_exp, _) :: _) = arg_typs in
    let instr_node = InstrNode.of_pnode node instr in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let listenerList_field_locs = Domain.Loc.append_fields this_locs ~fn:mListenerListField in
    (* this.listenerList -w-> values_to_add *)
    let listener_values, listener_diff =
      Domain.read_locs astate (listenerList_field_locs, this_diff)
    in
    let values_to_add, values_to_add_diff = Domain.eval astate node instr arg_exp in
    let symdiff = SymDiff.join listener_diff values_to_add_diff in
    let value = AbsVal.join listener_values values_to_add in
    [(DiffVal.empty, Domain.store_locs instr_node listenerList_field_locs (value, symdiff) astate)]


  let getListenerList astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let instr_node = InstrNode.of_pnode node instr in
    let this_locs, symdiff = Domain.eval_lv astate node instr this_exp in
    let listenerList_field_locs = Domain.Loc.append_fields this_locs ~fn:mListenerListField in
    let listener_values, symdiff = Domain.read_locs astate (listenerList_field_locs, symdiff) in
    let abstyp = AbsTyp.make_instance (Typ.mk_array Typ.pointer_to_java_lang_object) in
    let astate, array = Domain.make_allocsite astate ~abstyp (Node.of_pnode node instr) in
    (* ret_id -> array, array[Top] -> values *)
    let index_loc =
      Domain.Loc.append_index (Domain.Loc.SymHeap array) ~index:Domain.Val.top_primitive
    in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let astate = Domain.store_loc instr_node index_loc (listener_values, symdiff) astate in
    [((AbsVal.singleton array, symdiff_default), astate)]
end

module Arrays = struct
  let asList astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((arg_exp, _) :: _) = arg_typs in
    (* arg_exp -> arg_locs
       arg_locs[Top] -> array_values
       ret_id -> l
       l.mElementsField -> array_values
       l.mIsEmpty -> array_values == {} *)
    let instr_node = InstrNode.of_pnode node instr in
    let arg_locs, symdiff = Domain.eval_lv astate node instr arg_exp in
    let array_value, symdiff =
      Domain.read_locs astate (Domain.Loc.append_indexs arg_locs, symdiff)
    in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let element_typ = Domain.read_typ_of_vals astate array_value in
    let astate, list_value =
      Domain.make_allocsite astate (Node.of_pnode node instr) ~abstyp:element_typ
    in
    let element_loc = Domain.Loc.append_field (Domain.Loc.SymHeap list_value) ~fn:mElementsField in
    let isEmpty_loc = Domain.Loc.append_field (Domain.Loc.SymHeap list_value) ~fn:mIsEmptyField in
    let isEmpty_value =
      if AbsVal.is_empty array_value then AbsVal.singleton Domain.Val.one else AbsVal.top_primitive
    in
    let astate =
      Domain.store_loc instr_node element_loc (array_value, symdiff) astate
      |> Domain.store_loc instr_node isEmpty_loc (isEmpty_value, symdiff)
    in
    [((AbsVal.singleton list_value, symdiff_default), astate)]
end

module Concurrent = struct
  let get astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let this_exp, _ = List.hd_exn arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mConcurrentField in
    let diffval = Domain.read_locs astate (field_locs, this_diff) in
    [(diffval, astate)]


  let newPool astate node instr ~instantiate:_ ~callee:_ _ =
    let instr_node = Node.of_pnode node instr in
    let abstyp = AbsTyp.make_exact Fl4aprModels.Concurrent.pool_typ in
    let astate, allocsite = Domain.make_allocsite astate ~abstyp instr_node in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    [((AbsVal.singleton allocsite, symdiff_default), astate)]


  let newThread2 astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let arg_value, arg_diff = Domain.eval astate node instr arg_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mRunnableField in
    let astate =
      Domain.store_locs instr_node field_locs (arg_value, SymDiff.join this_diff arg_diff) astate
    in
    [(DiffVal.empty, astate)]


  let newThread3 astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: _ :: (arg_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let arg_value, arg_diff = Domain.eval astate node instr arg_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mRunnableField in
    let astate =
      Domain.store_locs instr_node field_locs (arg_value, SymDiff.join this_diff arg_diff) astate
    in
    [(DiffVal.empty, astate)]


  let start astate node instr ~instantiate ~callee:_ arg_typs =
    let program = Program.from_marshal () in
    let instr_node = Node.of_pnode node instr in
    let callees = Program.callees_of_instr_node program instr_node in
    let ret_id, arg_id = (tmp_ret_id, tmp_arg_id) in
    let[@warning "-8"] [(this_exp, _)] = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mRunnableField in
    let runnable_diffval = Domain.read_locs astate (field_locs, this_diff) in
    let astate = Domain.store_reg arg_id runnable_diffval astate in
    let run_arg_typs = [(Exp.Var arg_id, Fl4aprModels.Concurrent.runnable_typ)] in
    List.concat_map callees ~f:(fun callee ->
        match instantiate astate (ret_id, Typ.void) run_arg_typs callee with
        | Some results ->
            let Location.{file; line} = Program.pdesc_of program callee |> Procdesc.get_loc in
            L.d_printfln "<a href=\"../../%s.html#LINE%d\">GO_TO_RUN</a>"
              (DB.source_file_encoding file) line ;
            List.map results ~f:(fun astate ->
                (DiffVal.empty, Domain.remove_temps astate [Var.of_id ret_id; Var.of_id arg_id]) )
        | None ->
            (* UNSOUND *)
            L.d_printfln "failed to execute thread's run(): %a" Procname.pp callee ;
            let astate = Domain.{astate with is_incomplete= true} in
            [(DiffVal.empty, Domain.remove_temps astate [Var.of_id ret_id; Var.of_id arg_id])] )


  let submit astate node instr ~instantiate ~callee:_ arg_typs =
    let program = Program.from_marshal () in
    let instr_node = Node.of_pnode node instr in
    let callees = Program.callees_of_instr_node program instr_node in
    let ret_id = tmp_ret_id in
    let[@warning "-8"] [_; (callable_exp, _)] = arg_typs in
    let call_arg_typs = [(callable_exp, Fl4aprModels.Concurrent.callable_typ)] in
    let abstyp = AbsTyp.make_exact Fl4aprModels.Concurrent.future_typ in
    let astate, future_value = Domain.make_allocsite astate ~abstyp instr_node in
    let future_loc = Loc.of_heap future_value |> Loc.append_field ~fn:mConcurrentField in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let future_diffval = (AbsVal.singleton future_value, symdiff_default) in
    List.concat_map callees ~f:(fun callee ->
        match instantiate astate (ret_id, Typ.pointer_to_java_lang_object) call_arg_typs callee with
        | Some results ->
            let Location.{file; line} = Program.pdesc_of program callee |> Procdesc.get_loc in
            L.d_printfln "<a href=\"../../%s.html#LINE%d\">GO_TO_CALL</a>"
              (DB.source_file_encoding file) line ;
            List.map results ~f:(fun astate ->
                let return_diffval = Domain.eval astate node instr (Exp.Var ret_id) in
                let astate = Domain.store_loc instr_node future_loc return_diffval astate in
                (future_diffval, Domain.remove_temps astate [Var.of_id ret_id]) )
        | None ->
            (* UNSOUND *)
            L.d_printfln "failed to execute thread's call()" ;
            let astate = Domain.{astate with is_incomplete= true} in
            let astate = Domain.store_loc instr_node future_loc DiffVal.empty astate in
            [(future_diffval, Domain.remove_temps astate [Var.of_id ret_id])] )
end

module Map = struct
  let get_values astate (this_locs, this_diff) =
    Domain.read_locs astate (Loc.append_fields ~fn:mValuesField this_locs, this_diff)


  let get_keys astate (this_locs, this_diff) =
    Domain.read_locs astate (Loc.append_fields ~fn:mKeysField this_locs, this_diff)


  let store_keys instr_node (this_locs, this_diff) (value, diff) =
    Domain.store_locs instr_node
      (Loc.append_fields ~fn:mKeysField this_locs)
      (value, SymDiff.join this_diff diff)


  let store_values instr_node (this_locs, this_diff) (value, diff) =
    Domain.store_locs instr_node
      (Loc.append_fields ~fn:mValuesField this_locs)
      (value, SymDiff.join this_diff diff)


  let put astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* this.keys := this.keys + { key }
     * this.values := this.values + { value }
     * return := { value , null } 
     *)
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: (key_exp, _) :: (value_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let key_diffval, value_diffval =
      ( Domain.eval astate node instr key_exp |> DiffVal.join (get_keys astate this_locs_diff)
      , Domain.eval astate node instr value_exp |> DiffVal.join (get_values astate this_locs_diff)
      )
    in
    let astate =
      store_keys instr_node this_locs_diff key_diffval astate
      |> store_values instr_node this_locs_diff value_diffval
    in
    [((AbsVal.add Val.null (fst value_diffval), snd value_diffval), astate)]


  let get astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* return :=  this.values +  { null } *)
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let values_value, values_diff = get_values astate this_locs_diff in
    [((AbsVal.add Val.null values_value, values_diff), astate)]


  let values astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* return := allocsite
     * allocsite.mElements := this.values + { null } *)
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let astate, allocsite = Domain.make_allocsite astate ~abstyp:Collection.abstyp instr_node in
    let values_diffval = get_values astate this_locs_diff in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let astate, _ =
      Collection.add_to_new_collection node instr
        ~this_locs_diff:(Loc.Set.singleton (Loc.of_heap allocsite), symdiff_default)
        ~value:values_diffval astate
    in
    [((AbsVal.singleton allocsite, symdiff_default), astate)]


  let remove astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: (key_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let keys_values, keys_diff = get_keys astate this_locs_diff in
    let keys_diff = SymDiff.join keys_diff (snd (Domain.eval astate node instr key_exp)) in
    let values_value, values_diff = get_values astate this_locs_diff in
    let symdiff = SymDiff.join keys_diff values_diff in
    let astate =
      store_keys instr_node this_locs_diff (keys_values, keys_diff) astate
      |> store_values instr_node this_locs_diff (values_value, symdiff)
    in
    [((AbsVal.top_primitive, symdiff), astate)]


  let init astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_locs_diff = Domain.eval_lv astate node instr this_exp in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let astate =
      store_keys instr_node this_locs_diff (AbsVal.empty, symdiff_default) astate
      |> store_values instr_node this_locs_diff (AbsVal.empty, symdiff_default)
    in
    [(DiffVal.empty, astate)]


  let newEmptyMap astate node instr ~instantiate:_ ~callee:_ _ =
    let instr_node = Node.of_pnode node instr in
    let astate, allocsite =
      Domain.make_allocsite astate ~abstyp:(AbsTyp.make_instance Fl4aprModels.Map.typ) instr_node
    in
    let value = AbsVal.singleton allocsite in
    let symdiff_default = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
    let astate =
      store_keys instr_node
        (Loc.from_vals value, symdiff_default)
        (AbsVal.empty, symdiff_default) astate
      |> store_values instr_node
           (Loc.from_vals value, symdiff_default)
           (AbsVal.empty, symdiff_default)
    in
    [((value, symdiff_default), astate)]
end

module MapBuilder = struct
  let init astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let instr_node = Node.of_pnode node instr in
    (* this.map := allocsite *)
    let this_exp, _ = List.hd_exn arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mMapField in
    let abstyp = AbsTyp.make_instance Fl4aprModels.MapBuilder.map_typ in
    let astate, allocsite = Domain.make_allocsite astate ~abstyp instr_node in
    let astate =
      Domain.store_locs instr_node field_locs (AbsVal.singleton allocsite, this_diff) astate
    in
    [(DiffVal.empty, astate)]


  let put astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* this.map -> loc (given)
     * loc.mKeys := loc.mKeys + key 
     * loc.mValues := loc.mValues + value
     * return := this
     *)
    let instr_node = Node.of_pnode node instr in
    let[@warning "-8"] ((this_exp, _) :: (key_exp, _) :: (value_exp, _) :: _) = arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mMapField in
    let map_value, map_diff = Domain.read_locs astate (field_locs, this_diff) in
    let map_locs = Loc.from_vals map_value in
    let key_locs = Loc.append_fields map_locs ~fn:mKeysField in
    let value_locs = Loc.append_fields map_locs ~fn:mValuesField in
    let key_diffval = Domain.eval astate node instr key_exp in
    let value_diffval = Domain.eval astate node instr value_exp in
    let astate =
      Map.store_keys instr_node (key_locs, map_diff) key_diffval astate
      |> Map.store_values instr_node (value_locs, map_diff) value_diffval
    in
    let return_diffval = Domain.eval astate node instr this_exp in
    [(return_diffval, astate)]


  let build astate node instr ~instantiate:_ ~callee:_ arg_typs =
    (* return := this.map *)
    let this_exp, _ = List.hd_exn arg_typs in
    let this_locs, this_diff = Domain.eval_lv astate node instr this_exp in
    let field_locs = Loc.append_fields this_locs ~fn:mMapField in
    let map_diffval = Domain.read_locs astate (field_locs, this_diff) in
    [(map_diffval, astate)]
end

module Preconditions = struct
  let exn_typ = Typ.Name.Java.from_string "java.lang.IllegalStateException" |> Typ.mk_struct

  let checkState astate node instr ~instantiate:_ ~callee arg_typs =
    let instr_node = Node.of_pnode node instr in
    let program = Program.from_marshal () in
    let procname = Node.get_proc_name instr_node in
    let arg_exp, _ = List.hd_exn arg_typs in
    let arg_val, arg_diff = Domain.eval astate node instr arg_exp in
    let passing_states =
      let is_org_flow = Domain.is_dynamic_normal astate instr_node in
      Domain.prune_by_binop instr_node ~is_org_flow Binop.Eq arg_val (AbsVal.singleton Val.one)
        arg_diff astate
    in
    let failing_states =
      let is_org_flow = if Domain.is_dynamic_throw astate instr_node |> is_yes then `Yes else `No in
      let ret_var = Procdesc.get_ret_var (Program.pdesc_of program procname) in
      Domain.prune_by_binop instr_node ~is_org_flow Binop.Eq arg_val (AbsVal.singleton Val.zero)
        arg_diff astate
      |> List.map ~f:(Domain.bind_exn_extern instr_node ret_var ~exn_typ callee [])
    in
    List.map (passing_states @ failing_states) ~f:(fun astate -> (DiffVal.empty, astate))


  let checkNotNull astate node instr ~instantiate:_ ~callee arg_typs =
    let instr_node = Node.of_pnode node instr in
    let program = Program.from_marshal () in
    let procname = Node.get_proc_name instr_node in
    let arg_exp, _ = List.hd_exn arg_typs in
    let arg_val, arg_diff = Domain.eval astate node instr arg_exp in
    let passing_states =
      let is_org_flow = Domain.is_dynamic_normal astate instr_node in
      Domain.prune_by_binop instr_node ~is_org_flow Binop.Ne arg_val (AbsVal.singleton Val.null)
        arg_diff astate
    in
    let failing_states =
      let is_org_flow = if Domain.is_dynamic_throw astate instr_node |> is_yes then `Yes else `No in
      let ret_var = Procdesc.get_ret_var (Program.pdesc_of program procname) in
      Domain.prune_by_binop instr_node ~is_org_flow Binop.Eq arg_val (AbsVal.singleton Val.null)
        arg_diff astate
      |> List.map ~f:(Domain.bind_exn_extern instr_node ret_var ~exn_typ callee [])
    in
    List.map (passing_states @ failing_states) ~f:(fun astate -> (DiffVal.empty, astate))
end

module Object = struct
  let hashCode astate node instr ~instantiate:_ ~callee:_ arg_typs =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let _, this_diff = Domain.eval astate node instr this_exp in
    [((AbsVal.top_primitive, this_diff), astate)]
end

let _dispatch : Fl4aprModels.t -> exec = function
  | MBuiltIn Fl4aprModels.BuiltIn.InstanceOf ->
      BuiltIn.instanceof
  | MBuiltIn Fl4aprModels.BuiltIn.Cast ->
      BuiltIn.cast
  | MBuiltIn Fl4aprModels.BuiltIn.UnwrapException ->
      BuiltIn.unwrap_exception
  | MBuiltIn Fl4aprModels.BuiltIn.GetArrayLength ->
      BuiltIn.get_array_length
  | MEnum Fl4aprModels.Enum.Ordinal ->
      Enum.ordinal
  | MClass Fl4aprModels.Class.Cast ->
      Class.cast
  | MClass Fl4aprModels.Class.NewInstance ->
      Class.newInstance
  | MCollection Fl4aprModels.Collection.Add ->
      Collection.add
  | MCollection Fl4aprModels.Collection.AddAtIndex ->
      Collection.add
  | MCollection Fl4aprModels.Collection.AddAll ->
      Collection.addAll
  | MCollection Fl4aprModels.Collection.AddAllAtIndex ->
      Collection.addAll
  | MCollection Fl4aprModels.Collection.Get ->
      Collection.get
  | MCollection Fl4aprModels.Collection.Contains ->
      Collection.contains
  | MCollection Fl4aprModels.Collection.EmptyEnumeration ->
      Collection.emptyCollection
  | MCollection Fl4aprModels.Collection.Enumeration ->
      Collection.enumeration_of
  | MCollection Fl4aprModels.Collection.HasNext ->
      Collection.hasNext
  | MCollection Fl4aprModels.Collection.Init ->
      Collection.init
  | MCollection Fl4aprModels.Collection.InitFromCol ->
      Collection.initFromCol
  | MCollection Fl4aprModels.Collection.IsEmpty ->
      Collection.isEmpty
  | MCollection Fl4aprModels.Collection.Iterator ->
      Collection.iterator
  | MCollection Fl4aprModels.Collection.NewEmptyCollection ->
      Collection.newEmptyCollection
  | MCollection Fl4aprModels.Collection.NewCollectionFromCol ->
      Collection.newCollectionFromCol
  | MCollection Fl4aprModels.Collection.NewCollectionFromArray ->
      Collection.newCollectionFromArray
  | MCollection Fl4aprModels.Collection.Next ->
      Collection.next
  | MCollection Fl4aprModels.Collection.ToArray ->
      Collection.toArray
  | MCollection Fl4aprModels.Collection.Of ->
      Collection._of
  | MCollection Fl4aprModels.Collection.CopyOf ->
      Collection.copyOf
  | MCollection Fl4aprModels.Collection.Remove ->
      Collection.remove
  | MSystem Fl4aprModels.System.CurrentTimeMillis ->
      System.currentTimeMillis
  | MSystem Fl4aprModels.System.Arraycopy ->
      System.arraycopy
  | MLang Fl4aprModels.Lang.Append ->
      Lang.append
  | MLang Fl4aprModels.Lang.Format ->
      Lang.format
  | MLang Fl4aprModels.Lang.Init ->
      Lang.init
  | MLang Fl4aprModels.Lang.InitDefault ->
      Lang.init_default
  | MLang Fl4aprModels.Lang.InitSize ->
      Lang.init_size
  | MLang Fl4aprModels.Lang.IsEmpty ->
      Lang.isEmpty
  | MLang Fl4aprModels.Lang.Length ->
      Lang.length
  | MLang Fl4aprModels.Lang.ToString ->
      Lang.toString
  | MLang Fl4aprModels.Lang.Contains ->
      Lang.contains
  | MWriter Fl4aprModels.Writer.Init ->
      Writer.init
  | MWriter Fl4aprModels.Writer.Append ->
      Writer.append
  | MWriter Fl4aprModels.Writer.Write ->
      Writer.write
  | MWriter Fl4aprModels.Writer.ToString ->
      Writer.toString
  | MPrintWriter Fl4aprModels.PrintWriter.InitNew ->
      PrintWriter.init_new
  | MPrintWriter Fl4aprModels.PrintWriter.InitArg ->
      PrintWriter.init_arg
  | MPrintWriter Fl4aprModels.PrintWriter.Append ->
      PrintWriter.append
  | MPrintWriter Fl4aprModels.PrintWriter.Write ->
      PrintWriter.write
  | MPrintWriter Fl4aprModels.PrintWriter.ToString ->
      PrintWriter.toString
  | MPrintWriter Fl4aprModels.PrintWriter.Println ->
      PrintWriter.println
  | MAssert Fl4aprModels.Assert.AssertEqualsConst ->
      Assert.assertEqualsConst
  | MAssert Fl4aprModels.Assert.AssertSame ->
      Assert.assertSame
  | MAssert Fl4aprModels.Assert.AssertEquals ->
      Assert.assertEquals
  | MAssert Fl4aprModels.Assert.Fail ->
      Assert.fail
  | MEventListenerList Fl4aprModels.EventListenerList.Add ->
      EventListenerList.add
  | MEventListenerList Fl4aprModels.EventListenerList.Init ->
      EventListenerList.init
  | MEventListenerList Fl4aprModels.EventListenerList.GetListenerList ->
      EventListenerList.getListenerList
  | MArrays Fl4aprModels.Arrays.AsList ->
      Arrays.asList
  | MConcurrent Fl4aprModels.Concurrent.NewPool ->
      Concurrent.newPool
  | MConcurrent Fl4aprModels.Concurrent.Submit ->
      Concurrent.submit
  | MConcurrent Fl4aprModels.Concurrent.Get ->
      Concurrent.get
  | MConcurrent Fl4aprModels.Concurrent.NewThread2 ->
      Concurrent.newThread2
  | MConcurrent Fl4aprModels.Concurrent.NewThread3 ->
      Concurrent.newThread3
  | MConcurrent Fl4aprModels.Concurrent.Start ->
      Concurrent.start
  | MMap Fl4aprModels.Map.Init ->
      Map.init
  | MMap Fl4aprModels.Map.NewEmptyMap ->
      Map.newEmptyMap
  | MMap Fl4aprModels.Map.Put ->
      Map.put
  | MMap Fl4aprModels.Map.Get ->
      Map.get
  | MMap Fl4aprModels.Map.Remove ->
      Map.remove
  | MMap Fl4aprModels.Map.Values ->
      Map.values
  | MMapBuilder Fl4aprModels.MapBuilder.Init ->
      MapBuilder.init
  | MMapBuilder Fl4aprModels.MapBuilder.Put ->
      MapBuilder.put
  | MMapBuilder Fl4aprModels.MapBuilder.Build ->
      MapBuilder.build
  | MPreconditions Fl4aprModels.Preconditions.CheckState ->
      Preconditions.checkState
  | MPreconditions Fl4aprModels.Preconditions.CheckNotNull ->
      Preconditions.checkNotNull
  | MObject Fl4aprModels.Object.HashCode ->
      Object.hashCode


let dispatch callee arg_typs =
  match Fl4aprModels.dispatch callee arg_typs with
  | Some model ->
      Some (_dispatch model)
  | None ->
      None


let exec_model astate node instr ~instantiate ~callee arg_typs =
  match dispatch callee (List.unzip arg_typs |> snd) with
  | Some exec ->
      exec astate node instr ~instantiate ~callee arg_typs
  | None ->
      []
