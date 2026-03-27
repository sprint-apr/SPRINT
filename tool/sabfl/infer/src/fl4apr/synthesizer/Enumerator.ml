open! IStd
open! Vocab
module L = Logging
module AE = ASTExp

let pgm = lazy (Program.from_marshal ())

type search_state = {available_holes: int; scope: Procname.t; e: AE.t; parent: search_state option}
[@@deriving compare]

let cache : (search_state, search_state list) Cache.t = Cache.create ()

let next_state ~e state = {state with e; parent= Some state}

let rec pp_search_state fmt {available_holes; e; parent} =
  match parent with
  | Some par ->
      F.fprintf fmt "<%d, %a>@,%a" available_holes AE.pp e pp_search_state par
  | None ->
      F.fprintf fmt "<%d, %a>" available_holes AE.pp e


let progress_search_state state =
  L.debug L.Analysis L.Verbose "Current search state: @[<v>{@,@[<v 2>  %a@]@,}@]@." pp_search_state
    state


let die_on_enum = L.die InternalError "This case never happens: (enum on %a@.)" AE.pp

let rec enum ?(filter = None) ({available_holes; scope; e} as state) : search_state list =
  progress_search_state state ;
  let states =
    match (e : AE.t) with
    | _ when Int.( < ) available_holes 0 ->
        []
    | _ when AE.is_terminal e ->
        [state]
    | Hole ty_opt ->
        Cache.find_or_compute cache state ~compute:(fun () ->
            List.concat_map
              ~f:(fun st' -> enum ~filter (next_state st' ~e:st'.e))
              (enum_hole scope ty_opt state) )
    | Unary (Unop.LNot, e') ->
        List.map
          (enum ~filter {state with e= e'})
          ~f:(fun st -> {st with e= Unary (Unop.LNot, st.e)})
    | Binary (((Binop.Eq | Binop.Lt) as bo), lhs, rhs) ->
        enum_binary state ~bo ~lhs ~rhs
    | Binary (bo, lhs, rhs) ->
        enum_complex
          ~mk_with_subterms:(fun subterms ->
            AE.Binary (bo, List.nth_exn subterms 0, List.nth_exn subterms 1) )
          state [lhs; rhs]
    | Ternary (cond, e_then, e_else) ->
        enum_complex
          ~mk_with_subterms:(fun subterms ->
            AE.Ternary (List.nth_exn subterms 0, List.nth_exn subterms 1, List.nth_exn subterms 2)
            )
          state [cond; e_then; e_else]
    | FieldAccess _ ->
        enum_field_access state
    | MethodCall _ ->
        enum_method_call state
    | _ ->
        die_on_enum e
  in
  match filter with None -> states | Some f -> List.filter ~f:(fun {e} -> f e) states


(* enumerate expressions for given hole in the current scope *)
and enum_hole mthd ty state =
  let this_class = Option.value_exn (Procname.get_class_type_name mthd) in
  let pkg = Typ.Name.Java.get_java_class_name_exn this_class >@ JavaClassName.package in
  let open AE in
  let terminals =
    let variables = List.map (Collector.Variables.collect mthd) ~f:of_var in
    let literals = List.map ~f:of_const (Collector.Literals.collect pkg) in
    let finite_literals = [null; lit_true; lit_false] in
    finite_literals @ variables @ literals |> List.filter ~f:(AE.maybe_subtype_of ~ty)
  in
  let non_terminals =
    let bases =
      [ DynamicAccess (mk_this mthd)
      ; StaticAccess (Filled this_class)
      ; DynamicAccess object_hole
      ; StaticAccess any_type_component_hole ]
    in
    let hole = Empty ty in
    let field_accesses = List.map bases ~f:(fun base -> FieldAccess {base; field_hole= hole}) in
    let method_calls =
      if state.available_holes >= 1 then
        List.map bases ~f:(fun base -> MethodCall {base; mthd_hole= hole; args_hole= None})
      else []
    in
    field_accesses @ method_calls
  in
  List.map non_terminals ~f:(fun e ->
      { state with
        e
      ; parent= Some state
      ; available_holes=
          ( if is_base_terminal (get_base_exn e) then state.available_holes
          else state.available_holes - 1 ) } )
  @ List.map terminals ~f:(fun e -> {state with e; parent= Some state})


and enum_binary state ~bo ~lhs ~rhs =
  let are_both_constants e1 e2 = AE.is_constant e1 && AE.is_constant e2 in
  let is_boolean_literal e = AE.equal e AE.lit_true || AE.equal e AE.lit_false in
  match[@warning "-8"] List.partition_tf [(`L, lhs); (`R, rhs)] ~f:(AE.is_terminal <<< snd) with
  | [(_, terminal)], [(_, nonterminal)] ->
      let otherside =
        enum ~filter:(Some (not <<< is_boolean_literal)) (next_state ~e:nonterminal state)
      in
      let ty_terminal = AE.typeof terminal in
      let filter {e= e_other} =
        (not (AE.equal terminal e_other))
        && (not (are_both_constants terminal e_other))
        && AE.maybe_subtype_of ~ty:ty_terminal e_other
      in
      List.filter_map otherside ~f:(fun ({e= e_other} as st') ->
          Option.some_if (filter st') (next_state st' ~e:(AE.Binary (bo, e_other, terminal))) )
  | [], [(_, lhs); (_, rhs)] ->
      (* This case must be ㅁ = ㅁ *)
      let lhs' = enum ~filter:(Some (not <<< is_boolean_literal)) (next_state ~e:lhs state) in
      List.concat_map
        ~f:(fun ({e= e_lhs} as st') -> enum {st' with e= AE.Binary (bo, e_lhs, rhs)})
        lhs'


and enum_field_access ({e; scope} as state) =
  let next e' = {state with e= e'; parent= Some state} in
  match (e : AE.t) with
  | FieldAccess ({base} as fa) when not (AE.is_base_terminal base) ->
      let base_states = enum_base state base in
      List.concat_map base_states ~f:(fun (available_holes, base') ->
          enum {state with available_holes; e= AE.FieldAccess {fa with base= base'}} )
  | FieldAccess ({base} as fa) -> (
      let enclosing_class = Option.value_exn (Procname.get_class_type_name scope) in
      match AE.get_class_of_base base with
      | Some base_class ->
          let ty = AE.typeof e in
          let fieldnames =
            Collector.Fields.collect base_class ~pred:(fun fn ->
                let Program.{is_static; typ} = Program.get_fieldinfo !!pgm fn in
                phys_equal (AE.is_static base) is_static
                && AE.Ty.maybe_subtype_of typ ty
                && AE.Accessibility.is_accessible_field ~base ~from:enclosing_class fn )
          in
          List.map fieldnames ~f:(fun fn -> AE.FieldAccess {fa with field_hole= Filled fn})
          |> List.map ~f:next
      | None ->
          [] )
  | _ ->
      die_on_enum e


and enum_method_call ({e; available_holes; scope} as state) =
  let enclosing_class = Option.value_exn (Procname.get_class_type_name scope) in
  let collect_methods base mthd_hole =
    let pred mthd =
      phys_equal (AE.is_static base)
        (Procname.Java.is_static mthd || Procname.Java.is_constructor mthd)
      && AE.Accessibility.is_accessible_method ~base ~from:enclosing_class mthd
      &&
      match (mthd_hole : Procname.Java.t AE.hole) with
      | _ when Typ.is_void (AE.Ty.get_return_type mthd) ->
          false
      | Filled _ ->
          die_on_enum e
      | Empty typ ->
          AE.Ty.maybe_subtype_of (AE.Ty.get_return_type mthd) typ
    in
    match AE.get_class_of_base base with
    | Some base_class ->
        Collector.Methods.collect base_class ~pred
        |> List.map ~f:(fun procname ->
               Procname.as_java_exn ~explanation:""
                 (Procname.replace_class (Procname.Java procname) base_class) )
    | None ->
        []
  in
  match (e : AE.t) with
  | MethodCall {base= DynamicAccess (Literal (String _))} ->
      (* do not invoke methods via string literals*)
      []
  | MethodCall ({base} as mc) when not (AE.is_base_terminal base) ->
      let base_states = enum_base state base in
      List.concat_map base_states ~f:(fun (available_holes, base') ->
          enum {state with available_holes; e= AE.MethodCall {mc with base= base'}} )
  | MethodCall ({base; mthd_hole; args_hole= None} as mc) ->
      (* methods and arguments holes are enumerated together *)
      let accessible_methods = collect_methods base mthd_hole in
      let method_calls, argument_lengths =
        List.map accessible_methods ~f:(fun mthd ->
            let arg_holes =
              List.map (Procname.Java.get_parameters mthd) ~f:(fun ty -> AE.Hole ty)
            in
            ( AE.MethodCall {mc with mthd_hole= Filled mthd; args_hole= Some arg_holes}
            , List.length arg_holes ) )
        |> List.unzip
      in
      List.fold2_exn ~init:[]
        ~f:(fun acc mcall length ->
          {available_holes= available_holes - length; scope; e= mcall; parent= Some state} :: acc )
        method_calls argument_lengths
      |> List.concat_map ~f:enum
  | MethodCall ({base; mthd_hole= Empty _; args_hole= Some args} as mc) ->
      (* case where methods arguments are determined in advance *)
      let accessible_methods = collect_methods base mc.mthd_hole in
      let signature_matched =
        List.filter
          ~f:(fun mthd ->
            match
              List.for_all2
                ~f:(fun param arg -> AE.Ty.maybe_subtype_of arg param)
                (Procname.Java.get_parameters mthd)
                (List.map args ~f:AE.typeof)
            with
            | Ok true ->
                true
            | _ ->
                false )
          accessible_methods
      in
      let mcalls =
        List.map signature_matched ~f:(fun mthd -> AE.MethodCall {mc with mthd_hole= Filled mthd})
      in
      List.concat_map mcalls ~f:(fun mcall -> enum (next_state state ~e:mcall))
  | MethodCall ({mthd_hole= Filled _; args_hole= Some args} as mc) ->
      enum_complex
        ~mk_with_subterms:(fun args' -> AE.MethodCall {mc with args_hole= Some args'})
        state args
  | _ ->
      die_on_enum e


and enum_base state base =
  match (base : AE.base) with
  | DynamicAccess e ->
      let filter = function
        | e when AE.is_null e ->
            false
        | AE.MethodCall {mthd_hole= Filled mthd} when Typ.is_void (AE.Ty.get_return_type mthd) ->
            false
        | _ ->
            true
      in
      let e_bases = enum (next_state state ~e) in
      List.filter e_bases ~f:(fun st -> filter st.e)
      |> List.map ~f:(fun {available_holes; e= e_base} ->
             (available_holes, AE.DynamicAccess e_base) )
  | StaticAccess _ ->
      (* Only the untyped static klass hole can be here *)
      let pkg =
        let this_class = Option.value_exn (Procname.get_class_type_name state.scope) in
        Typ.Name.Java.get_java_class_name_exn this_class >@ JavaClassName.package
      in
      List.map (Collector.Classes.collect pkg) ~f:(fun cls ->
          (state.available_holes, AE.StaticAccess (Filled cls)) )


and enum_complex ~mk_with_subterms state subterms =
  let first_nonterminal_idx, term =
    List.find_mapi_exn subterms ~f:(fun idx e -> Option.some_if (not (AE.is_terminal e)) (idx, e))
  in
  List.map
    ~f:(fun ({e= e'} as st') ->
      let subterms' =
        List.mapi subterms ~f:(fun idx e -> if Int.( = ) idx first_nonterminal_idx then e' else e)
      in
      next_state st' ~e:(mk_with_subterms subterms') )
    (enum (next_state state ~e:term))


let enum_expressions ?(terminals_only = true) ?(initial_expression = AE.any_type_hole) ~max_cost
    scope =
  let initial_state =
    { available_holes= max_cost - AE.number_of_holes initial_expression
    ; scope
    ; e= initial_expression
    ; parent= None }
  in
  List.filter_map
    ~f:(fun {e} -> Option.some_if ((not terminals_only) || AE.is_terminal e) e)
    (enum initial_state)
  |> AE.Set.of_list |> AE.Set.elements


let enum_default ty =
  let open AE.Literal in
  match ty with
  | _ when Typ.equal ty Typ.boolean ->
      AE.Literal (Boolean false)
  | _ when Typ.equal ty Typ.int ->
      AE.Literal (Integer IntLit.zero)
  | _ when Typ.equal ty Typ.long ->
      AE.Literal (Integer IntLit.zero)
  | _ when Typ.equal ty Typ.double ->
      AE.Literal (Float 0.0)
  | _ when Typ.equal ty Typ.float ->
      AE.Literal (Float 0.0)
  | _ when Typ.is_pointer ty ->
      AE.Literal NULL
  | _ ->
      L.die InternalError "No default value for type %a@." (Typ.pp_full Pp.text) ty
