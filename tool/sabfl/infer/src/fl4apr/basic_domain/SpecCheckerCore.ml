open! Vocab
module F = Format
module L = Logging
module CFG = ProcCfg.Exceptional
module Node = InstrNode
module Models = BasicDom.Models
module AbsTyp = BasicDom.AbsTyp
module Symbol = SymDom.Symbol
module AbsVal = SymDom.AbsVal
module Val = SymDom.SymVal

module type Summary = sig
  module Domain = SpecCheckerDomain

  type t

  type analysis_data

  type get_summary = Procname.t -> t option

  val pp : Format.formatter -> t -> unit

  val empty : t

  val instantiate_summary :
       Program.t
    -> Domain.t
    -> analysis_data
    -> Procdesc.Node.t
    -> Sil.instr
    -> Ident.t * Typ.t
    -> (Exp.t * Typ.t) list
    -> Procname.t
    -> Domain.t list option

  val to_summary : Procdesc.t -> Domain.t list -> t

  val get_disjuncts : t -> Domain.t list

  val get_only_normals : t -> t
end

module Make (Summary : Summary) = struct
  module CFG = CFG
  module Domain = SpecCheckerDomain
  module Disjunct = Domain.Disjunct
  module SymDiff = Domain.SymDiff

  type analysis_data =
    { program: Program.t
    ; interproc: Summary.analysis_data
    ; abs_patches: Fault.Set.t InstrNode.Map.t
    ; dyninfo: DynInfo.NodeMap.t }

  let analysis_data interproc procname : analysis_data =
    let program =
      match Sys.is_file Program.marshalled_path with
      | `No | `Unknown ->
          (* generate models *)
          Program.from_marshal () ~init:true
      | `Yes ->
          Program.from_marshal ()
    in
    if is_sprint then
      let add_fault node fault acc =
        match InstrNode.Map.find_opt node acc with
        | Some abs_patches ->
            InstrNode.Map.add node (Fault.Set.add fault abs_patches) acc
        | None ->
            InstrNode.Map.add node (Fault.Set.singleton fault) acc
      in
      let abs_patches =
        ( if Config.sprint_exnchecker then Fault.from_marshal ()
        else Fault.from_marshal ~path:"abs_patches_to_analyze.data" () )
        |> List.filter ~f:(Procname.equal procname <<< Fault.get_proc_name)
        |> List.fold ~init:InstrNode.Map.empty ~f:(fun acc fault ->
               let instr_node = Fault.get_location_node Fault.(fault.loc) in
               match (Node.get_instr instr_node, fault) with
               | Sil.Call (ret_id, fexp, arg_typs, location, callflags), _ ->
                   let instr1 =
                     Sil.Call (ret_id, fexp, arg_typs, location, {callflags with cf_virtual= false})
                   in
                   let instr2 =
                     Sil.Call (ret_id, fexp, arg_typs, location, {callflags with cf_virtual= true})
                   in
                   let node1, node2 =
                     (Node.{instr_node with instr= instr1}, Node.{instr_node with instr= instr2})
                   in
                   add_fault node1 fault acc |> add_fault node2 fault
               | Sil.Prune (bexp, _, _, _), Fault.{desc= WrongExp _} ->
                   let instr_node_neg =
                     Node.pnode_of instr_node |> Procdesc.Node.get_preds
                     |> List.concat_map ~f:Procdesc.Node.get_succs
                     |> List.find_map_exn ~f:(fun pnode ->
                            Instrs.find_map (Procdesc.Node.get_instrs pnode) ~f:(function
                              | Sil.Prune (UnOp (Unop.LNot, bexp', _), _, _, _) as instr
                                when Exp.equal bexp bexp' ->
                                  Some (InstrNode.of_pnode pnode instr)
                              | _ ->
                                  None ) )
                   in
                   add_fault instr_node fault acc |> add_fault instr_node_neg fault
               | _ ->
                   add_fault instr_node fault acc )
      in
      let dyninfo =
        DynInfo.NodeMap.filter
          (fun x _ -> Node.get_proc_name x |> Procname.equal procname)
          (DynInfo.from_marshal ())
      in
      {program; interproc; abs_patches; dyninfo}
    else {program; interproc; abs_patches= InstrNode.Map.empty; dyninfo= DynInfo.NodeMap.empty}


  let init_uninitialized_fields callee arg_typs node instr astate =
    match callee with
    | Procname.Java mthd -> (
        let cls = Procname.Java.get_class_type_name mthd in
        match Tenv.load_global () with
        | Some tenv -> (
          match Tenv.lookup tenv cls with
          | Some Struct.{fields} ->
              let instr_node = Node.of_pnode node instr in
              let base_exp, _ = List.hd_exn arg_typs in
              let base_loc, symdiff = Domain.eval_lv astate node instr base_exp in
              if SymDiff.is_diff symdiff && not (Domain.is_original astate) then
                L.d_printfln " - state with %a should update unintialized fields" Domain.pp_sig
                  astate ;
              List.fold fields ~init:astate ~f:(fun acc (fn, fn_typ, _) ->
                  let field_locs = Domain.Loc.append_fields ~fn base_loc in
                  (* should_update && not in mem: initialize *)
                  (* default values are independent from any values *)
                  let uninit_locs =
                    Domain.Loc.Set.filter
                      (fun l ->
                        match Domain.(astate.last_org) with
                        | Original ->
                            not Domain.(Mem.mem l astate.mem)
                        | Current (_, org_state) | Past (_, org_state) ->
                            not Domain.(Mem.mem l astate.mem || Mem.mem l org_state.mem) )
                      field_locs
                  in
                  let default_value =
                    Domain.Val.get_default_by_typ fn_typ |> Domain.AbsVal.singleton
                  in
                  Domain.store_locs instr_node uninit_locs (default_value, symdiff) acc )
          | None ->
              astate )
        | None ->
            astate )
    | _ ->
        astate


  let rec exec_prune ~is_org_flow astate node instr bexp =
    let instr_node = Node.of_pnode node instr in
    match bexp with
    | Exp.BinOp (binop, e1, e2) ->
        let value1, symdiff1 = Domain.eval astate node instr e1 in
        let value2, symdiff2 = Domain.eval astate node instr e2 in
        let symdiff = SymDiff.join symdiff1 symdiff2 in
        Domain.prune_by_binop ~is_org_flow instr_node binop value1 value2 symdiff astate
    | Exp.UnOp (Unop.LNot, Exp.BinOp (binop, e1, e2), _) -> (
      match Binop.negate binop with
      | Some binop' ->
          exec_prune ~is_org_flow astate node instr (Exp.BinOp (binop', e1, e2))
      | None ->
          let _, symdiff1 = Domain.eval astate node instr e1 in
          let _, symdiff2 = Domain.eval astate node instr e2 in
          let symdiff = SymDiff.join symdiff1 symdiff2 in
          Domain.check_dynamic_flow instr_node ~is_org_flow symdiff astate )
    | Exp.Var _ as e ->
        let value, symdiff = Domain.eval astate node instr e in
        let true_value = Domain.AbsVal.singleton Domain.Val.one in
        Domain.prune_by_binop ~is_org_flow instr_node Binop.Eq value true_value symdiff astate
    | Exp.UnOp (Unop.LNot, (Exp.Var _ as e), _) ->
        let value, symdiff = Domain.eval astate node instr e in
        let false_value = Domain.AbsVal.singleton Domain.Val.zero in
        Domain.prune_by_binop ~is_org_flow instr_node Binop.Eq value false_value symdiff astate
    | e ->
        L.d_printfln "execute non-logical instruction %a" pp_instr instr ;
        let _, symdiff = Domain.eval astate node instr e in
        Domain.check_dynamic_flow instr_node ~is_org_flow symdiff astate


  let throw_uncaught_exn ~is_dynamic_throw astate node instr (value, symdiff) =
    let instr_node = Node.of_pnode node instr in
    let proc_desc = Program.pdesc_of (Program.from_marshal ()) (Procdesc.Node.get_proc_name node) in
    let ret_var = Procdesc.get_ret_var proc_desc in
    let null = AbsVal.singleton Val.null in
    let exn_typ_str = "java.lang.NullPointerException" in
    let is_org_flow = is_dynamic_throw in
    if is_yes is_dynamic_throw then
      (* HEURISTICS: follow NPE execution when test fails by NPE *)
      Domain.prune_by_binop ~is_org_flow instr_node Binop.Eq value null symdiff astate
      |> List.map ~f:(Domain.throw_exn instr_node ret_var ~exn_typ_str)
    else []


  let add_non_null_constraints ~is_dynamic_normal node instr (_, symdiff) astate =
    let instr_node = Node.of_pnode node instr in
    let null = AbsVal.singleton Val.null in
    let is_org_flow = is_dynamic_normal in
    (* ignore null-checking here, it is ineffective and unsound *)
    Domain.prune_by_binop ~is_org_flow instr_node Binop.Eq null null symdiff astate


  let check_null astate node instr e =
    let instr_node = Node.of_pnode node instr in
    let is_dynamic_throw = Domain.is_dynamic_throw astate instr_node in
    let is_dynamic_normal =
      (* die-info is ambiguous for checking NPE *)
      `Unknown
    in
    L.d_printfln "check dynamic flow before null checking: %a, %a" pp_three_value is_dynamic_normal
      pp_three_value is_dynamic_throw ;
    match e with
    | Exp.Lvar _ | Exp.Lindex _ ->
        (* TODO: deal with null.f, null[x] cases
         * Currently, we assume _.f and _[] location is non-null *)
        ([], [astate])
    | Exp.Lfield (Exp.Lvar _, _, _) | Exp.Lfield (Exp.Const _, _, _) ->
        (* Global.field, "".value: not null *)
        ([], [astate])
    | Exp.Lfield (e', _, _) | e' ->
        let v = Domain.eval astate node instr e' in
        let null_states = throw_uncaught_exn ~is_dynamic_throw astate node instr v in
        let non_null_states = add_non_null_constraints ~is_dynamic_normal node instr v astate in
        (null_states, non_null_states)


  let check_oob program dyninfo astate node instr symdiff =
    let instr_node = Node.of_pnode node instr in
    L.d_printfln "Dynamic info: %a" AbsBool.pp
      (Domain.find_dynamic_exprs ~dyninfo astate instr_node) ;
    let exn_states =
      if Domain.is_dynamic_throw ~dyninfo astate instr_node |> is_yes then
        let proc_desc = Program.pdesc_of program (Procdesc.Node.get_proc_name node) in
        let ret_var = Procdesc.get_ret_var proc_desc in
        Domain.prune_by_binop ~is_org_flow:`Yes instr_node Binop.Eq AbsVal.zero AbsVal.zero symdiff
          astate
        |> List.map
             ~f:
               (Domain.throw_exn instr_node ret_var
                  ~exn_typ_str:"java.lang.ArrayIndexOutOfBoundsException" )
      else []
    in
    let normal_states =
      let is_org_flow = Domain.is_dynamic_normal ~dyninfo astate instr_node in
      Domain.prune_by_binop ~is_org_flow instr_node Binop.Eq AbsVal.zero AbsVal.zero symdiff astate
    in
    (exn_states, normal_states)


  let exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee =
    L.d_printfln "FAILED to resolve call or get summary. exec unknown call" ;
    let instr_node = Node.of_pnode node instr in
    let arg_diff_values =
      List.map arg_typs ~f:(fun (arg_exp, arg_typ) ->
          if is_array arg_typ then
            let arg_locs, arg_diff = Domain.eval_lv astate node instr arg_exp in
            let index_locs = Domain.Loc.append_indexs arg_locs in
            Domain.read_locs astate (index_locs, arg_diff)
          else
            (* HEURISTICS: check impact of abs_patches only for arguments, excluding their fields *)
            Domain.eval astate node instr arg_exp )
    in
    let symdiff =
      List.fold (List.unzip arg_diff_values |> snd) ~init:SymDiff.empty ~f:SymDiff.join
    in
    let is_dynamic_throw = Domain.is_dynamic_throw astate instr_node in
    let normal_states () =
      if Program.is_primitive_type ret_typ then
        [Domain.store_reg ret_id (AbsVal.top_primitive, symdiff) astate]
      else if Typ.is_void ret_typ then
        match instr with
        | Sil.Call (_, _, (Var id, _) :: _, _, {cf_virtual}) when cf_virtual ->
            let value, _ = Domain.eval astate node instr (Var id) in
            [Domain.store_reg id (value, symdiff) astate]
        | _ ->
            [astate]
      else
        let abstyp = AbsTyp.make_instance ret_typ in
        [ Domain.bind_extern_value_absval instr_node (ret_id, ret_typ) ~abstyp callee
            arg_diff_values astate ]
    in
    let exceptional_states () =
      L.d_printfln "unknown call returns exceptions" ;
      let pdesc = Program.pdesc_of (Program.from_marshal ()) (Procdesc.Node.get_proc_name node) in
      let ret_var = Procdesc.get_ret_var pdesc in
      let abstyp = AbsTyp.exn_typ in
      [Domain.bind_exn_extern_absval instr_node ret_var ~abstyp callee arg_diff_values astate]
    in
    if is_yes is_dynamic_throw then
      (if SymDiff.is_diff symdiff then normal_states () else []) @ exceptional_states ()
    else normal_states ()


  let is_usable_fieldname ret_typ fn =
    (* check if T(a.field) = T(a.getField()) 
     *       or T(a.field) = T(arg) for arg in a.setField(arg) *)
    match Program.get_field_typ_opt fn with
    | Some fn_typ ->
        AbsTyp.(is_different (Some (make_instance ret_typ)) (Some (make_instance fn_typ))) |> not
    | _ ->
        true


  let exec_unknown_getter astate node instr callee (ret_id, ret_typ) arg_typs =
    (* Modeling getter method (e.g., p.getField() returns p.field) *)
    let this_exp, this_typ = List.hd_exn arg_typs in
    let fieldname =
      String.chop_prefix_exn (Procname.get_method callee) ~prefix:"get" |> String.uncapitalize
    in
    match Typ.(this_typ.desc) with
    | Tptr ({desc= Tstruct name}, _)
      when is_usable_fieldname ret_typ (Fieldname.make name fieldname) ->
        let field_name = Fieldname.make name fieldname in
        L.d_printfln "execute getter by fieldname %a" Fieldname.pp field_name ;
        let this_values, symdiff = Domain.eval astate node instr this_exp in
        let astate_result =
          Domain.AbsVal.fold
            (fun this_value astate_acc ->
              let this_type_loc =
                Domain.Loc.append_field ~fn:field_name (Domain.Loc.SymHeap this_value)
              in
              if Domain.(Mem.mem this_type_loc astate_acc.mem) then
                let value, symdiff = Domain.read_loc astate_acc (this_type_loc, symdiff) in
                Domain.store_reg_weak ret_id (value, symdiff) astate
              else
                let new_value =
                  Domain.Val.make_uninterpret callee [this_value] |> Domain.AbsVal.singleton
                in
                Domain.store_typ new_value (AbsTyp.make_instance ret_typ) astate
                |> Domain.store_reg_weak ret_id (new_value, symdiff) )
            this_values astate
        in
        [astate_result]
    | _ ->
        L.d_printfln "failed to get fieldname for %a, execute by unknown_call"
          (Typ.pp_full (Pp.html Pp.Black))
          this_typ ;
        exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee


  let exec_unknown_setter astate node instr callee (ret_id, ret_typ) arg_typs =
    (* Modeling getter method (e.g., p.getField() returns p.field) *)
    let instr_node = Node.of_pnode node instr in
    let this_exp, this_typ = List.hd_exn arg_typs in
    let _, arg_typ = List.nth_exn arg_typs 1 in
    let fieldname =
      String.chop_prefix_exn (Procname.get_method callee) ~prefix:"set" |> String.uncapitalize
    in
    match Typ.(this_typ.desc) with
    | Tptr ({desc= Tstruct name}, _)
      when is_usable_fieldname arg_typ (Fieldname.make name fieldname) ->
        let field_name = Fieldname.make name fieldname in
        L.d_printfln "execute getter by fieldname %a" Fieldname.pp field_name ;
        let this_values, this_diff = Domain.eval astate node instr this_exp in
        let[@warning "-8"] arg_values, arg_diff =
          match arg_typs with
          | [_; (arg_exp, _)] ->
              Domain.eval astate node instr arg_exp
          | _ :: arg_typs ->
              let arg_values =
                List.map arg_typs ~f:(fun (arg_exp, _) -> Domain.eval astate node instr arg_exp)
              in
              Domain.make_uninterpret_absval astate callee arg_values
        in
        let symdiff = SymDiff.join this_diff arg_diff in
        let this_field_locs =
          Domain.Loc.append_fields ~fn:field_name (Domain.Loc.from_vals this_values)
        in
        [Domain.store_locs instr_node this_field_locs (arg_values, symdiff) astate]
    | _ ->
        exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee


  let exec_unknown_newSet astate node instr _ (ret_id, _) arg_typs =
    (* Modeling getter method (e.g., p.newHashSet() returns empty set) *)
    let instr_node = Node.of_pnode node instr in
    let abstyp = AbsTyp.make_instance Fl4aprModels.Collection.typ in
    let astate, value = Domain.make_allocsite astate instr_node ~abstyp in
    match arg_typs with
    | [(arg_exp, Typ.{desc= Tptr ({desc= Tstruct name}, _)})]
    | [(arg_exp, Typ.{desc= Tstruct name})]
      when Fl4aprModels.Collection.implements name ->
        (* newSet(arg) => copy elements of arg to the new set *)
        let arg_locs, arg_diff = Domain.eval_lv astate node instr arg_exp in
        let this_locs = Domain.Loc.from_vals (Domain.AbsVal.singleton value) in
        let is_empty_value, is_empty_diff =
          let locs = Domain.Loc.append_fields arg_locs ~fn:mIsEmptyField in
          Domain.read_locs astate (locs, arg_diff)
        in
        let elements_value, elements_diff =
          let locs = Domain.Loc.append_fields arg_locs ~fn:mElementsField in
          Domain.read_locs astate (locs, arg_diff)
        in
        let symdiff = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
        astate
        |> Domain.store_locs instr_node
             (Domain.Loc.append_fields this_locs ~fn:mIsEmptyField)
             (is_empty_value, SymDiff.join arg_diff is_empty_diff)
        |> Domain.store_locs instr_node
             (Domain.Loc.append_fields this_locs ~fn:mElementsField)
             (elements_value, SymDiff.join arg_diff elements_diff)
        |> Domain.store_reg ret_id (Domain.AbsVal.singleton value, symdiff)
    | [] | [_] ->
        let symdiff = if Domain.has_past_original astate then SymDiff.diff else SymDiff.empty in
        astate
        |> SpecCheckerModels.Collection.setIsEmpty node instr
             (Domain.Loc.from_vals (Domain.AbsVal.singleton value), symdiff)
        |> Domain.store_reg ret_id (Domain.AbsVal.singleton value, symdiff)
    | _ ->
        L.(die InternalError) "not here"


  let exec_clone astate node instr callee (ret_id, _) arg_typs =
    L.d_printfln "exec clone" ;
    let open Domain in
    let this_exp, _ = List.hd_exn arg_typs in
    let this_value, this_diff = Domain.eval astate node instr this_exp in
    let this_locs = Loc.from_vals this_value in
    let relevant_locs =
      AbsVal.fold
        (fun v acc ->
          match v with
          | Val.VSymbol s -> (
            match Symbol.default_typ_opt s |> Option.map ~f:(strip_ptr <<< AbsTyp.typ_of) with
            | Some Typ.{desc= Tstruct name} -> (
              match Tenv.lookup (Program.tenv ()) name with
              | Some Struct.{fields} ->
                  List.fold fields ~init:acc ~f:(fun acc (fn, _, _) ->
                      Loc.append_fields this_locs ~fn |> Loc.Set.union acc )
              | None ->
                  acc )
            | Some Typ.{desc= Tarray _} ->
                Loc.append_indexs this_locs |> Loc.Set.union acc
            | _ ->
                acc )
          | _ ->
              acc )
        this_value Loc.Set.empty
      |> Mem.fold
           (fun l _ acc -> if Loc.Set.mem (Loc.base_of l) this_locs then Loc.Set.add l acc else acc)
           astate.mem
    in
    let _, symdiff = Domain.read_locs astate (relevant_locs, this_diff) in
    let diffval = Domain.make_uninterpret_absval astate callee [(this_value, symdiff)] in
    [Domain.store_reg ret_id diffval astate]


  (* Handle unknown method with generic modeling *)
  let exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee =
    let callee_name = Procname.get_method callee in
    let result =
      match instr with
      | Sil.Call (_, _, [(_, arg_typ)], _, _)
        when Typ.is_pointer arg_typ && String.is_prefix callee_name ~prefix:"get" ->
          (* model only getter without arguments *)
          exec_unknown_getter astate node instr callee (ret_id, ret_typ) arg_typs
      | Sil.Call (_, _, [_], _, _) when String.equal callee_name "clone" ->
          exec_clone astate node instr callee (ret_id, ret_typ) arg_typs
      | Sil.Call (_, _, ((_, arg_typ) :: _ :: _ as arg_typs), _, _)
        when Typ.is_pointer arg_typ
             && String.is_prefix callee_name ~prefix:"set"
             && Typ.is_void ret_typ ->
          exec_unknown_setter astate node instr callee (ret_id, ret_typ) arg_typs
      | Sil.Call (_, _, arg_typs, _, {cf_virtual})
        when (not cf_virtual)
             && String.is_prefix callee_name ~prefix:"new"
             && String.is_suffix callee_name ~suffix:"Set"
             && List.length arg_typs <= 1 ->
          [exec_unknown_newSet astate node instr callee (ret_id, ret_typ) arg_typs]
      | Sil.Call (_, Const (Cfun (Java mthd)), (Exp.Var id, _) :: _, _, _)
        when Procname.is_constructor callee ->
          let value, symdiff = Domain.eval astate node instr (Exp.Var id) in
          let new_value = Val.make_uninterpret Models.extern_alloc [AbsVal.choose value] in
          let typ = Typ.mk_struct (Procname.Java.get_class_type_name mthd) in
          let astate =
            Domain.store_reg id (AbsVal.singleton new_value, symdiff) astate
            |> Domain.store_typ (AbsVal.singleton new_value) (AbsTyp.make_exact typ)
          in
          exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee
      | Sil.Call (_, _, (Exp.Var id, _) :: _, _, _)
        when String.is_prefix callee_name ~prefix:"traverse" ->
          (* Handle visitor pattern: recursively set mElements to symbol *)
          let instr_node = Node.of_pnode node instr in
          let base_locs, symdiff = Domain.eval_lv astate node instr (Exp.Var id) in
          let reachable_locs, reachable_vals =
            Domain.compute_reachability_from_base astate ~base_locs ~base_vals:AbsVal.empty
          in
          (* Set data dependency: use reachable values to define reachable locs *)
          let symdiff =
            SymDiff.join symdiff (SymDiff.of_uses (Disjunct.of_values reachable_vals))
          in
          (* Update locations with only trivial values *)
          let normal_state =
            Domain.Loc.Set.fold
              (fun l acc ->
                let vals, symdiff = Domain.read_loc astate (l, symdiff) in
                match AbsVal.is_singleton_or_more vals with
                | Singleton v when Val.is_concrete v && Val.is_primitive v ->
                    Domain.store_locs instr_node (Domain.Loc.Set.singleton l)
                      (AbsVal.top_primitive, symdiff) acc
                | Singleton v when Val.is_concrete v ->
                    Domain.store_locs instr_node (Domain.Loc.Set.singleton l) (AbsVal.top, symdiff)
                      acc
                | Empty ->
                    Domain.store_locs instr_node (Domain.Loc.Set.singleton l) (AbsVal.top, symdiff)
                      acc
                | _ ->
                    acc )
              reachable_locs astate
          in
          let exn_states =
            exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee
            |> List.filter ~f:Domain.is_exceptional
          in
          normal_state :: exn_states
      | _ ->
          (* HEURISTICS: do not symbolize return value of extern functions *)
          exec_unknown_call astate node instr (ret_id, ret_typ) arg_typs callee
    in
    L.d_printfln
      "*** No summary found, %d states are returned by analyzing it as uninterpretted function... \
       ***"
      (List.length result) ;
    result


  let exec_by_summary astate ~interproc node instr (ret_id, ret_typ) arg_typs callee =
    let program = Program.from_marshal () in
    match
      Summary.instantiate_summary program astate interproc node instr (ret_id, ret_typ) arg_typs
        callee
    with
    | Some results when Procname.is_constructor callee ->
        ( if Config.debug_mode then
          let Location.{file; line} = Program.pdesc_of program callee |> Procdesc.get_loc in
          L.d_printfln "<a href=\"../../%s.html#LINE%d\">GO_TO_CALLEE</a>"
            (DB.source_file_encoding file) line ) ;
        let exn_states, normal_states = List.partition_tf ~f:Domain.is_exceptional results in
        let normal_posts =
          if Config.sprint_exnchecker then normal_states
          else List.map normal_states ~f:(init_uninitialized_fields callee arg_typs node instr)
        in
        exn_states @ normal_posts
    | Some results ->
        ( if Config.debug_mode then
          let Location.{file; line} = Program.pdesc_of program callee |> Procdesc.get_loc in
          L.d_printfln "<a href=\"../../%s.html#LINE%d\">GO_TO_CALLEE</a>"
            (DB.source_file_encoding file) line ) ;
        results
    | None when Domain.is_original astate && not (Typ.is_void ret_typ) ->
        let all_uses =
          Domain.IdUse.fold (fun _ use -> Disjunct.join use) Domain.(astate.id_use) Disjunct.empty
          |> Domain.LocUse.fold (fun _ use -> Disjunct.join use) Domain.(astate.loc_use)
        in
        L.d_printfln
          "FAILED to get summary because of recursiveness, so update full uses to ret_id by %a"
          Disjunct.pp all_uses ;
        let astate = Domain.{astate with is_incomplete= true} in
        let disjuncts = exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee in
        List.map disjuncts ~f:(fun astate ->
            Domain.{astate with id_use= Domain.IdUse.weak_update ret_id all_uses astate.id_use} )
    | None ->
        L.d_printfln "FAILED to get summary because of recursiveness" ;
        let astate = Domain.{astate with is_incomplete= true} in
        exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee


  let exec_interproc_call astate {interproc; program} node instr (ret_id, ret_typ) arg_typs callees
      =
    let is_all_undef = List.for_all callees ~f:(Program.is_undef_proc program) in
    let instr_node = Node.of_pnode node instr in
    let callees =
      if is_all_undef then callees
      else List.filter callees ~f:(not <<< Program.is_undef_proc program)
    in
    L.d_printfln "try to analyze callees: %a from %a@." (Pp.seq Procname.pp) callees Domain.pp_sig
      astate ;
    let analyze_single callee =
      match SpecCheckerModels.dispatch callee (List.map ~f:snd arg_typs) with
      | Some exec ->
          L.d_printfln "execute model function" ;
          let instantiate astate (ret_id, ret_typ) arg_typs callee =
            Summary.instantiate_summary program astate interproc node instr (ret_id, ret_typ)
              arg_typs callee
          in
          let results = exec ~instantiate astate node instr ~callee arg_typs in
          List.map results ~f:(fun (diffval, astate) -> Domain.store_reg ret_id diffval astate)
      | None when Program.is_undef_proc program callee ->
          L.d_printfln "%a is undefined procedure" Procname.pp callee ;
          exec_unknown_method astate node instr (ret_id, ret_typ) arg_typs callee
      | None ->
          exec_by_summary ~interproc astate node instr (ret_id, ret_typ) arg_typs callee
    in
    if List.is_empty callees then
      L.(die InternalError) "no callees at %a@." Node.pp (Node.of_pnode node instr) ;
    let results = List.concat_map callees ~f:analyze_single in
    if Domain.is_original astate && Domain.is_dynamic_throw astate instr_node |> is_yes then
      List.filter results ~f:(fun post_state ->
          (not (Domain.is_original post_state)) || Domain.is_exceptional post_state )
    else results


  let exec_interproc_call astate analysis_data node instr ret_typ arg_typs callees =
    match instr with
    | Sil.Call (_, Const (Cfun (Procname.Java mthd)), _, _, {cf_virtual}) when cf_virtual ->
        let callees =
          if List.is_empty callees then (* bottom-up callgraph analysis *)
            [Procname.Java mthd]
          else callees
        in
        let callees =
          if
            List.is_empty callees && Program.is_undef_proc analysis_data.program (Procname.Java mthd)
          then [Procname.Java mthd]
          else callees
        in
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs callees
    | _ ->
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs callees


  (** compute post states for a given instruction and a state *)
  let compute_posts ({program; dyninfo} as analysis_data) node instr astate =
    let instr_node = Node.of_pnode node instr in
    match instr with
    | Sil.Load {id; e} when Ident.is_none id ->
        (* instruction for null-dereference effect in virtual invocation *)
        let null_states, non_null_states = check_null astate node instr e in
        if Domain.is_original astate && Domain.is_dynamic_throw astate instr_node |> is_yes then
          null_states
        else null_states @ non_null_states
    | Sil.Load {id; e= Lindex _ as e} ->
        let locs, symdiff = Domain.eval_lv astate node instr e in
        (* symbolic location is introduced if location is unknown *)
        let value, symdiff = Domain.read_locs astate (locs, symdiff) in
        let exn_states, normal_states = check_oob program dyninfo astate node instr symdiff in
        let normal_states = List.map normal_states ~f:(Domain.store_reg id (value, symdiff)) in
        normal_states @ exn_states
    | Sil.Load {id; e= Lfield (_, fn, _) as e; typ}
      when Program.is_nonnull_static_final_field fn && Typ.is_pointer typ ->
        (* ASSUMPTION: final static field is not null! *)
        let locs, symdiff = Domain.eval_lv astate node instr e in
        let value, symdiff = Domain.read_locs astate (locs, symdiff) in
        Domain.store_reg id (value, symdiff) astate
        |> Domain.store_typ value (AbsTyp.make_instance typ)
        |> add_non_null_constraints ~is_dynamic_normal:`Yes node instr (value, symdiff)
    | Sil.Load {id; e} ->
        let locs, symdiff = Domain.eval_lv astate node instr e in
        (* symbolic location is introduced if location is unknown *)
        let null_states, non_null_states = check_null astate node instr e in
        let non_null_states =
          let value, symdiff = Domain.read_locs astate (locs, symdiff) in
          List.map non_null_states ~f:(Domain.store_reg id (value, symdiff))
        in
        null_states @ non_null_states
    | Sil.Store {e1; e2= Exp.BinOp (Binop.PlusA _, x, Const (Cint y))}
      when IntLit.isone y || IntLit.isminusone y ->
        (* i' = i + 1 => i' = Top *)
        let locs, symdiff1 = Domain.eval_lv astate node instr e1 in
        let _, symdiff2 = Domain.eval astate node instr x in
        let symdiff = SymDiff.join symdiff1 symdiff2 in
        let value = (* TODO: precise modeling for + *) AbsVal.top_primitive in
        Domain.store_locs instr_node locs (value, symdiff) astate
        |> Domain.prune_by_binop ~is_org_flow:`Yes instr_node Binop.Lt value value symdiff
    | Sil.Store {e1; e2= Exp.Exn _ as e2} ->
        let locs, symdiff1 = Domain.eval_lv astate node instr e1 in
        let value, symdiff2 = Domain.eval astate node instr e2 in
        let symdiff = SymDiff.join symdiff1 symdiff2 in
        [Domain.store_locs instr_node locs (value, symdiff) astate |> Domain.set_exception]
    | Sil.Store {e1= Exp.Lindex _ as e1; e2} ->
        let locs, symdiff1 = Domain.eval_lv astate node instr e1 in
        let value, symdiff2 = Domain.eval astate node instr e2 in
        let exn_states, normal_states = check_oob program dyninfo astate node instr symdiff1 in
        let symdiff = SymDiff.join symdiff1 symdiff2 in
        let normal_states =
          List.map normal_states ~f:(Domain.store_locs instr_node locs (value, symdiff))
        in
        exn_states @ normal_states
    | Sil.Store {e1= Exp.Lvar pv as e1; e2} when Pvar.is_frontend_tmp pv ->
        let locs, symdiff1 = Domain.eval_lv astate node instr e1 in
        let value, symdiff2 = Domain.eval astate node instr e2 in
        let symdiff = SymDiff.join symdiff1 symdiff2 in
        [Domain.store_locs instr_node locs (value, symdiff) astate]
    | Sil.Store {e1= Exp.Lvar pv; e2= Exp.Const (Cint intlit)}
      when Pvar.is_return pv && IntLit.isnull intlit && is_exn_handler node ->
        [astate]
    | Sil.Store {e1; e2} ->
        let locs, symdiff1 = Domain.eval_lv astate node instr e1 in
        let null_states, non_null_states = check_null astate node instr e1 in
        let non_null_states =
          let value, symdiff2 = Domain.eval astate node instr e2 in
          let symdiff = SymDiff.join symdiff1 symdiff2 in
          List.map non_null_states ~f:(Domain.store_locs instr_node locs (value, symdiff))
        in
        null_states @ non_null_states
    | Sil.Call
        ( (ret_id, ret_typ)
        , Const (Cfun proc)
        , [(Exp.Sizeof ({typ= {desc= Tarray {elt}} as typ; dynamic_length} as sizeof_data), arg_typ)]
        , loc
        , cf )
      when is_new proc ->
        (* allocation instruction *)
        let astate, value =
          Domain.make_allocsite astate ~abstyp:(AbsTyp.make_exact typ) instr_node
        in
        let astate, elt_value =
          if is_array elt then
            let elt_alloc_instr =
              Sil.Call
                ( (ret_id, ret_typ)
                , Const (Cfun proc)
                , [(Sizeof {sizeof_data with typ= elt}, arg_typ)]
                , loc
                , cf )
            in
            Domain.make_allocsite astate ~abstyp:(AbsTyp.make_exact elt)
              (Node.of_pnode node elt_alloc_instr)
          else if is_primitive_wrapper_typ elt then (astate, Val.top_primitive)
          else (astate, Val.null)
        in
        let index_locs =
          Domain.Loc.from_vals (AbsVal.singleton value) |> Domain.Loc.append_indexs
        in
        let _, symdiff = Domain.eval_opt astate node instr dynamic_length in
        [ Domain.store_reg ret_id (Domain.AbsVal.singleton value, symdiff) astate
          |> Domain.store_locs instr_node index_locs (AbsVal.singleton elt_value, symdiff) ]
    | Sil.Call
        ( (ret_id, _)
        , Const (Cfun proc)
        , [(Exp.Sizeof {typ= {desc= Tstruct name}; dynamic_length}, _)]
        , _
        , _ )
      when is_new proc && String.is_suffix ~suffix:"Type" (Typ.Name.name name) ->
        (* FIXME: HEURISTICS *)
        let _, symdiff = Domain.eval_opt astate node instr dynamic_length in
        let absval = Val.make_absfun (Procname.from_string_c_fun "Type") [] |> AbsVal.singleton in
        [Domain.store_reg ret_id (absval, symdiff) astate]
    | Sil.Call ((ret_id, _), Const (Cfun proc), [(Exp.Sizeof {typ; dynamic_length}, _)], _, _)
      when is_new proc ->
        (* allocation instruction *)
        let astate, value =
          Domain.make_allocsite astate ~abstyp:(AbsTyp.make_exact typ) instr_node
        in
        let _, symdiff = Domain.eval_opt astate node instr dynamic_length in
        [Domain.store_reg ret_id (Domain.AbsVal.singleton value, symdiff) astate]
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual}) when not cf_virtual ->
        (* static call *)
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs [proc]
    | Sil.Call (ret_typ, Const (Cfun proc), arg_typs, _, {cf_virtual})
      when cf_virtual && Typ.is_int (List.hd_exn arg_typs |> snd) ->
        (* Pasring ERROR: callee is virtual, but invoke it by integer *)
        exec_unknown_method astate node instr ret_typ arg_typs proc
    | Sil.Call (ret_typ, Const (Cfun proc), ((this_exp, _) :: _ as arg_typs), _, {cf_virtual})
      when cf_virtual ->
        (* virtual call *)
        (* TODO: use dynamic info when this_value is original_value *)
        let _, symdiff = Domain.eval astate node instr this_exp in
        let dyn_class_info =
          DynInfo.get_class_info ~dyninfo Domain.(astate.current_ctxs) instr_node
        in
        let callees =
          if Typ.Name.Set.is_empty dyn_class_info || SymDiff.is_diff symdiff then
            Program.callees_of_instr_node program instr_node
          else
            let callees = Program.resolve_methods proc dyn_class_info in
            if List.is_empty callees then (
              L.d_printfln "FAILED to resolve dynamic callee information: %a" Typ.Name.Set.pp
                dyn_class_info ;
              Program.callees_of_instr_node program instr_node )
            else (
              L.d_printfln "found dynamic callee information:@. - class info: %a@. - callees: %a"
                Typ.Name.Set.pp dyn_class_info (Pp.seq ~sep:"," Procname.pp) callees ;
              callees )
        in
        exec_interproc_call astate analysis_data node instr ret_typ arg_typs callees
    | Sil.Call _ ->
        (* callback call *)
        L.(die InternalError) "unknown callee at %a@." Node.pp instr_node
    | Sil.Prune (bexp, _, _, _) ->
        let is_org_flow = Domain.is_dynamic_normal astate instr_node in
        L.d_printfln "dynamic exprs: %a" AbsBool.pp (Domain.find_dynamic_exprs astate instr_node) ;
        exec_prune ~is_org_flow astate node instr bexp
    | Sil.Metadata (ExitScope (vars, _)) ->
        let vars_to_remove =
          List.filter vars ~f:(function Var.LogicalVar _ -> true | _ -> false)
        in
        [Domain.remove_temps astate vars_to_remove]
    | Sil.Metadata (Nullify (pv, _)) when Domain.Loc.of_pvar pv |> Domain.Loc.is_temp ->
        [Domain.remove_temps astate [Var.of_pvar pv]]
    | Sil.Metadata (Nullify (_, _)) ->
        (* skip removing pvar to correctly resolve control-dependency *)
        [astate]
    | Sil.Metadata (Abstract _) | Sil.Metadata Skip | Sil.Metadata (VariableLifetimeBegins _) ->
        [astate]


  let compute_hole_posts org_state astate analysis_data node instr abs_patches =
    let instr_node = InstrNode.of_pnode node instr in
    let program = analysis_data.program in
    let pdesc = Program.pdesc_of program (Procdesc.Node.get_proc_name node) in
    let modify_field pv fn astate =
      if String.equal "*" (Fieldname.get_field_name fn) then
        let open Domain in
        let pv_heap = Domain.read_loc astate (Domain.Loc.of_pvar pv, SymDiff.diff) |> fst in
        match Program.get_pvar_typ_opt pv with
        | Some Typ.{desc= Tptr ({desc= Tarray {elt}}, _)} ->
            let field_locs = Domain.Loc.from_vals pv_heap |> Domain.Loc.append_indexs in
            let value = Domain.make_hole astate instr_node ~typ:elt |> Domain.AbsVal.singleton in
            store_locs instr_node field_locs (value, SymDiff.diff) astate
        | _ ->
            Mem.fold
              (fun l v acc ->
                if AbsVal.disjoint v pv_heap then acc
                else store_loc instr_node l (v, SymDiff.diff) acc )
              org_state.mem astate
      else
        let pv_heap =
          Domain.read_loc astate (Domain.Loc.of_pvar pv, SymDiff.diff)
          |> fst |> Domain.Loc.from_vals
        in
        let field_locs = Domain.Loc.append_fields pv_heap ~fn in
        let value =
          match Program.get_field_typ_opt fn with
          | Some typ ->
              Domain.make_hole astate instr_node ~typ |> Domain.AbsVal.singleton
          | None ->
              Domain.AbsVal.(join unknown top_primitive)
        in
        Domain.store_locs instr_node field_locs (value, SymDiff.diff) astate
    in
    if Fault.Set.is_empty abs_patches |> not then
      L.debug L.Analysis L.Quiet " -- Captured fault: [%a]@." Fault.Set.pp abs_patches ;
    Fault.Set.fold
      (fun (Fault.{desc; loc; new_instrs} as fault) acc ->
        let astate = Domain.set_fault ~fault astate in
        let post =
          match (desc, loc) with
          | ShouldSkip, _ ->
              let astate = Domain.{astate with last_org= Past (instr_node, org_state)} in
              (if Config.sprint_no_test then compute_posts analysis_data node instr astate else [])
              @ [Domain.set_conditional astate]
          | MissingSideEffect (pv, fn), Before _ -> (
            try modify_field pv fn astate |> compute_posts analysis_data node instr
            with _ -> (* If pvar is tmp, pv could be removed in memory *)
                      [] )
          | MissingSideEffect (pv, fn), After _ -> (
            try compute_posts analysis_data node instr astate |> List.map ~f:(modify_field pv fn)
            with _ -> (* If pvar is tmp, pv could be removed in memory *)
                      [] )
          | MissingSideEffect _, Inplace _ | MissingSideEffect _, Range _ ->
              []
          | WrongExp _, _ ->
              let astate = Domain.{astate with last_org= Past (instr_node, org_state)} in
              List.fold new_instrs ~init:[astate] ~f:(fun disjuncts new_instr ->
                  match new_instr with
                  | Sil.Load {id; e= Exp.Cast (_, hole); typ} when Fault.is_hole hole ->
                      let value =
                        Domain.make_hole astate instr_node ~typ |> Domain.AbsVal.singleton
                      in
                      List.map disjuncts ~f:(Domain.store_reg id (value, SymDiff.diff))
                  | Sil.Store {e1= Exp.Cast (_, hole)} when Fault.is_hole hole ->
                      []
                  | _ ->
                      List.concat_map disjuncts ~f:(compute_posts analysis_data node new_instr) )
          | MissingErrorHandling (`Throw Typ.{desc= Tstruct name}), _ ->
              let astate = Domain.{astate with last_org= Past (instr_node, org_state)} in
              let ret_var = Procdesc.get_ret_var pdesc in
              (if Config.sprint_no_test then compute_posts analysis_data node instr astate else [])
              @ [Domain.throw_exn instr_node ret_var ~exn_typ_str:(Typ.Name.name name) astate]
          | MissingErrorHandling (`Throw _), _ ->
              L.(die InternalError) "Invalid Fault"
          | MissingErrorHandling `Return, _ ->
              let astate = Domain.{astate with last_org= Past (instr_node, org_state)} in
              let new_symval =
                Domain.make_hole astate instr_node ~typ:(Procdesc.get_ret_type pdesc)
                |> AbsVal.singleton
              in
              let results =
                if Typ.is_void (Procdesc.get_ret_type pdesc) then [Domain.set_conditional astate]
                else
                  let ret_var_loc = Procdesc.get_ret_var pdesc |> Domain.Loc.of_pvar in
                  [ Domain.store_loc instr_node ret_var_loc (new_symval, SymDiff.diff) astate
                    |> Domain.set_conditional ]
              in
              (if Config.sprint_no_test then compute_posts analysis_data node instr astate else [])
              @ results
        in
        post @ acc )
      abs_patches []


  let _astates_with_no_patch_here astate ~abs_patches =
    match Domain.(astate.abs_patches) with
    | None ->
        Some astate
    | Some pre_abs_patches ->
        let abs_patches_unrelated = Fault.Set.diff pre_abs_patches abs_patches in
        if Fault.Set.is_empty abs_patches_unrelated then None
        else Some (Domain.set_abs_patches astate ~abs_patches:(Some abs_patches_unrelated))


  let exec_fault analysis_data node instr ~abs_patches astate =
    let instr_node = InstrNode.of_pnode node instr in
    let pre_state = astate in
    let org_state, astate =
      match Domain.(astate.last_org) with
      | Current (_, org_state) | Past (_, org_state) ->
          (org_state, astate)
      | Original ->
          (pre_state, Domain.set_diff instr_node pre_state)
    in
    let post_states_meeting_hole =
      match Domain.(pre_state.abs_patches) with
      | None when Domain.is_original pre_state ->
          let ctxs_wo_dummy = Domain.(Contexts.remove Context.dummy pre_state.current_ctxs) in
          if Domain.Contexts.is_empty ctxs_wo_dummy then []
          else
            compute_hole_posts org_state
              (Domain.set_ctx astate ctxs_wo_dummy)
              analysis_data node instr abs_patches
      | None ->
          []
      | Some pre_abs_patches ->
          let abs_patches_to_meet = Fault.Set.inter pre_abs_patches abs_patches in
          if Fault.Set.is_empty abs_patches_to_meet then []
          else compute_hole_posts org_state astate analysis_data node instr abs_patches_to_meet
    in
    post_states_meeting_hole


  let _split_on_control_deps astate ~dyninfo node instr =
    let instr_node = Node.of_pnode node instr in
    if is_prune_instr instr then
      match DynInfo.get_br_info ~dyninfo Domain.(astate.current_ctxs) instr_node with
      | AbsBool.Top ->
          [ Domain.
              {astate with control_deps= ControlDeps.update instr_node (V true) astate.control_deps}
          ; Domain.
              {astate with control_deps= ControlDeps.update instr_node (V false) astate.control_deps}
          ]
      | _ ->
          [astate]
    else
      match DynInfo.get_die_info ~dyninfo Domain.(astate.current_ctxs) instr_node with
      | AbsBool.Top ->
          [ Domain.
              {astate with control_deps= ControlDeps.update instr_node (V true) astate.control_deps}
          ; Domain.
              {astate with control_deps= ControlDeps.update instr_node (V false) astate.control_deps}
          ]
      | AbsBool.V false ->
          [ Domain.
              {astate with control_deps= ControlDeps.update instr_node (V false) astate.control_deps}
          ]
      | _ ->
          [astate]


  let _prepare_state_delta astate {dyninfo} node instr =
    if Config.sprint_exnchecker || Config.sprint_no_test then
      (* force control dependency *)
      let open Domain in
      let last_org =
        match astate.last_org with
        | Original ->
            Original
        | Current (node, org_state) | Past (node, org_state) ->
            Past (node, org_state)
      in
      [{astate with last_org}]
    else if Domain.has_dummy_ctx astate then [astate]
    else _split_on_control_deps astate ~dyninfo node instr


  let _is_invalid_state astate node instr =
    let has_invalid_type astate =
      AbsTyp.is_invalid
        (AbsVal.fold
           (fun v acc ->
             let open Domain in
             if VTMap.mem v astate.vtmap then
               let abstyp = VTMap.find v astate.vtmap in
               if AbsTyp.is_bottom acc then abstyp
               else if AbsTyp.equal abstyp acc then acc
               else AbsTyp.invalid
             else acc )
           Domain.(astate.important_param)
           AbsTyp.bottom )
    in
    (* State with unexpected flow (e.g., unhandled exception) *)
    let is_unused_irvar pv =
      Instrs.exists (Procdesc.Node.get_instrs node) ~f:(function
        | Sil.Metadata (Nullify (pv', _)) ->
            Pvar.equal pv pv'
        | _ ->
            false )
    in
    let has_invalid_reg astate =
      match instr with
      | Sil.Load {e= Var id} when Domain.is_unknown_id astate id ->
          true
      | Sil.Store {e1= Lvar pv; e2= Var id} when Domain.is_unknown_id astate id ->
          not (is_unused_irvar pv)
      | Sil.Store {e2= Var id} when Domain.is_unknown_id astate id ->
          true
      | Sil.Call (_, _, arg_typs, _, _) ->
          let contains_unknown_id (arg_exp, _) =
            match arg_exp with Exp.Var id -> Domain.is_unknown_id astate id | _ -> false
          in
          List.exists arg_typs ~f:contains_unknown_id
      | _ ->
          false
    in
    let has_invalid_mem astate =
      match (instr, Domain.(astate.last_org)) with
      | Sil.Load {e= Lvar pv}, Domain.Past (_, org_state) when Domain.has_skip_fault astate ->
          let loc = Domain.Loc.of_pvar pv in
          not Domain.(Mem.mem loc astate.mem || Mem.mem loc org_state.mem)
      | _ ->
          false
    in
    match Domain.(astate.last_org) with
    | _ when has_invalid_type astate ->
        L.d_printfln "@.state %a is pruned because has inequal vtmap:@.%a@." Domain.pp_sig astate
          Domain.VTMap.pp
          Domain.(astate.vtmap) ;
        true
    | (Current (_, org_state) | Past (_, org_state))
      when has_invalid_reg org_state && has_invalid_reg astate ->
        L.d_printfln "%a has invalid register" Domain.pp_sig astate ;
        true
    | (Current _ | Past _) when has_invalid_mem astate ->
        L.d_printfln "%a is invalidated becauseof invalid skip patch" Domain.pp_sig astate ;
        true
    | Original when has_invalid_reg astate ->
        L.d_printfln "%a has invalid register" Domain.pp_sig astate ;
        true
    | _ ->
        false


  let exec_instr astate analysis_data node instr =
    if Domain.is_exceptional astate && not (is_exn_handler node) then
      (* If a state is exceptional, skip non_exn_handling instructions *)
      [astate]
    else if _is_invalid_state astate node instr then
      (* FIXME: remove it and implement normal heuristics *)
      []
    else
      let pre_states = _prepare_state_delta astate analysis_data node instr in
      let instr_node = Node.of_pnode node instr in
      match InstrNode.Map.find_opt instr_node analysis_data.abs_patches with
      | Some _ when (not Config.sprint_exnchecker) && Domain.has_dummy_ctx astate ->
          (* record prestate for patch-injected nodes *)
          Utils.with_file_out
            (F.asprintf "%s/%a" Config.sprint_invmap_dir InstrNode.pp_id instr_node) ~f:(fun oc ->
              Marshal.to_channel oc astate [] ) ;
          List.concat_map pre_states ~f:(compute_posts analysis_data node instr)
      | Some abs_patches ->
          let posts_with_no_patch_here =
            (* case for astate with patch info {p1, p2}, but p1.node != node *)
            pre_states
            |> List.filter_map ~f:(_astates_with_no_patch_here ~abs_patches)
            |> List.concat_map ~f:(compute_posts analysis_data node instr)
          in
          posts_with_no_patch_here
          @ List.concat_map pre_states ~f:(exec_fault analysis_data node instr ~abs_patches)
      | None ->
          List.concat_map pre_states ~f:(compute_posts analysis_data node instr)


  let exec_instr astate analysis_data cfg_node instr =
    let node = CFG.Node.underlying_node cfg_node in
    let posts = debug_time "exec_instr" ~f:(exec_instr astate analysis_data node) ~arg:instr in
    Verify.check_instr astate node instr posts ;
    posts


  let pp_session_name node fmt =
    F.fprintf fmt "===== Spec Checker (%a) ====@." Procdesc.Node.pp (CFG.Node.underlying_node node)
end
