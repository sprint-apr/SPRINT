open! IStd
open! Vocab
module F = Format
module AE = ASTExp
module Domain = SpecCheckerDomain
module Summary = SpecCheckerSummary
module AbsVal = Domain.AbsVal
module Val = Domain.Val
module Loc = Domain.Loc
module Symbol = SymDom.Symbol
module SymDiff = Domain.SymDiff

exception OutOfScopeExn

let pgm = lazy (Program.from_marshal ())

type invariant_map = SpecChecker.Analyzer.invariant_map

type expectation = Equal of AE.t * AE.t | NotEqual of AE.t * AE.t

let pp_expectation fmt = function
  | Equal (e1, e2) ->
      F.fprintf fmt "(%a) = (%a)" AE.pp e1 AE.pp e2
  | NotEqual (e1, e2) ->
      F.fprintf fmt "(%a) != (%a)" AE.pp e1 AE.pp e2


let get_expressions = function Equal (e1, e2) | NotEqual (e1, e2) -> [e1; e2]

let get_original_value contexts faulty_node e_org : AbsBool.t =
  match (DynInfo.get_br_info contexts faulty_node, InstrNode.get_instr faulty_node) with
  | V dyninfo, Sil.Prune (bexp, _, _, _) when Exp.equal bexp e_org ->
      AbsBool.V dyninfo
  | V dyninfo, _ ->
      AbsBool.negate (V dyninfo)
  | _ ->
      AbsBool.Top


let generate_expectations contexts patch =
  let Patch.{kind; location; procname} = patch in
  let pdesc = Program.pdesc_of (Program.from_marshal ()) procname in
  let exp_for_context context =
    let contexts = Domain.Contexts.singleton context in
    match kind with
    | ExpReplacement {e_org; e_rep} -> (
        let faulty_node = Fault.get_location_node location in
        let dyn_branch_value = get_original_value contexts faulty_node e_org in
        if Config.debug_mode then
          L.progress "Dynamic branch value for %a: %a@." Domain.Contexts.pp contexts AbsBool.pp
            dyn_branch_value ;
        match (dyn_branch_value, AE.from_IR_exp_opt pdesc e_org, e_rep) with
        | V true, Some ae_org, Binary (Binop.LAnd, ae1, ae2) when AE.equal ae2 ae_org ->
            (* false = true && HOLE => HOLE = false *)
            [Equal (ae1, AE.Literal (AE.Literal.Boolean false))]
        | V true, Some ae_org, Binary (Binop.LOr, _, ae2) when AE.equal ae2 ae_org ->
            (* false = true || HOLE => X *)
            [Equal (AE.Literal (AE.Literal.Boolean true), AE.Literal (AE.Literal.Boolean false))]
        | V false, Some ae_org, Binary (Binop.LAnd, _, ae2) when AE.equal ae2 ae_org ->
            (* true = false && HOLE => X *)
            [Equal (AE.Literal (AE.Literal.Boolean true), AE.Literal (AE.Literal.Boolean false))]
        | V false, Some ae_org, Binary (Binop.LOr, ae1, ae2) when AE.equal ae2 ae_org ->
            (* true = false || HOLE => HOLE = true *)
            [Equal (ae1, AE.Literal (AE.Literal.Boolean true))]
        | (V false | V true), Some _, Binary ((Binop.LOr | Binop.LAnd), _, _) ->
            (* true = false || HOLE => HOLE = true *)
            [Equal (AE.Literal (AE.Literal.Boolean true), AE.Literal (AE.Literal.Boolean false))]
        | V dyn_branch_value, _, _ ->
            [Equal (e_rep, AE.Literal (AE.Literal.Boolean (not dyn_branch_value)))]
        | _ -> (
          try [NotEqual (e_rep, AE.from_IR_exp (Program.pdesc_of !!pgm procname) e_org)]
          with _ -> [] ) )
    | InsertHandle {cond} | SkipStmt {cond} ->
        [Equal (cond, AE.lit_true)]
    | _ ->
        []
  in
  Domain.Contexts.fold
    (fun context acc ->
      let result = exp_for_context context in
      (* L.progress "expectation for %a, %a: %a@." Domain.Context.pp context Patch.pp patch (Pp.seq pp_expectation) result ; *)
      result @ acc )
    contexts []


let resolve_callees base_typ mthd with_dummy_ctx =
  let callees_with_body =
    match base_typ with
    | _ when not with_dummy_ctx ->
        Program.callee_dispatch
          ~base_class:(Procname.Java.get_class_type_name mthd)
          ~is_exact:true mthd
    | BasicDom.AbsTyp.Exact Typ.{desc= Tstruct name} ->
        Program.callee_dispatch ~base_class:name ~is_exact:true mthd
    | BasicDom.AbsTyp.Instance Typ.{desc= Tstruct name} ->
        Program.callee_dispatch ~base_class:name ~is_exact:false mthd
    | _ ->
        Program.callee_dispatch
          ~base_class:(Procname.Java.get_class_type_name mthd)
          ~is_exact:false mthd
  in
  if Procname.Set.is_empty callees_with_body then Procname.Set.singleton (Procname.Java mthd)
  else callees_with_body


let top_value = AbsVal.join AbsVal.top_primitive (AbsVal.singleton (Val.VAbstract AbsHeap))

let read_locs memory locs =
  try Domain.read_locs memory (locs, SymDiff.empty) |> fst with _ -> raise OutOfScopeExn


(* Loc.Set.fold
   (fun l ->
     match l with
     | Loc.Var _ | Loc.TempVar _ -> (
       try Domain.read_loc memory (l, SymDiff.empty) |> fst |> AbsVal.join
       with e ->
         L.progress "Mem: %a@." Domain.pp memory ;
         L.progress "failed to read %a@." Loc.pp l ;
         raise e (* raise OutOfScopeExn  *) )
     | _ -> (
       try Domain.read_loc memory (l, SymDiff.empty) |> fst |> AbsVal.join with _ -> AbsVal.join AbsVal.top ) )
   locs AbsVal.empty *)

let nonnull_absval = Val.make_absfun (Procname.from_string_c_fun "FL4APR_Nonnull") []

let is_sat memory (vals1, vals2, binop, instr_node) =
  match (AbsVal.is_singleton_or_more vals1, AbsVal.is_singleton_or_more vals2, binop) with
  | Singleton v, Singleton Val.VNull, Binop.Eq when Val.equal nonnull_absval v ->
      false
  | Singleton Val.VNull, Singleton v, Binop.Eq when Val.equal nonnull_absval v ->
      false
  | _ ->
      Domain.is_sat_assert memory (vals1, vals2, binop, instr_node)


let get_return astate =
  let proc = Domain.(astate.current_proc) in
  let pdesc = Program.pdesc_of (Program.from_marshal ()) proc in
  let ret_var = Procdesc.get_ret_var pdesc in
  match Domain.read_loc_opt astate (Domain.Loc.of_pvar ret_var) with
  | Some vals ->
      vals
  | None ->
      AbsVal.empty


let is_defined_cache = ref Procname.Map.empty

let is_defined mthd =
  match Procname.Map.find_opt (Procname.Java mthd) !is_defined_cache with
  | Some v ->
      v
  | None ->
      let result =
        match Procdesc.load (Procname.Java mthd) with
        | Some pdesc ->
            (Procdesc.get_attributes pdesc).is_defined
        | None ->
            false
      in
      is_defined_cache := Procname.Map.add (Procname.Java mthd) result !is_defined_cache ;
      result


let is_nonnull_mthd base_typ mthd args =
  let program = Program.from_marshal () in
  if Program.is_primitive_type (Procname.Java.get_return_typ mthd) then false
  else if AE.Method.is_constructor mthd then true
  else if NullnessAnalysis.is_nonnull_mthd mthd args then true
  else if String.equal "append" (Procname.Java.get_method mthd) then true
  else if is_defined mthd then Program.is_nonnull_proc program (Procname.Java mthd)
  else
    let callees =
      match (strip_ptr base_typ).Typ.desc with
      | Tstruct base_class ->
          (* callee could be extern or interface *)
          Program.callee_dispatch ~base_class mthd ~is_exact:false
      | _ ->
          Procname.Set.empty
    in
    if Procname.Set.is_empty callees then (
      (* in case of extern *)
      L.progress "could not find callees from [%a] %a@." (Typ.pp_full Pp.text) base_typ Procname.pp
        (Procname.Java mthd) ;
      false )
    else
      (* L.progress "check nonnullness for %a in %a@." Procname.pp (Procname.Java mthd) Procname.Set.pp callees ; *)
      Procname.Set.for_all (Program.is_nonnull_proc program) callees


let is_constant_mthd base_typ mthd =
  let program = Program.from_marshal () in
  let callees =
    match (strip_ptr base_typ).Typ.desc with
    | Tstruct base_class ->
        (* callee could be extern or interface *)
        Program.callee_dispatch ~base_class mthd ~is_exact:false
    | _ ->
        Procname.Set.empty
  in
  if Procname.Set.is_empty callees then (
    (* in case of extern *)
    L.progress "could not find callees from [%a] %a@." (Typ.pp_full Pp.text) base_typ Procname.pp
      (Procname.Java mthd) ;
    false )
  else
    (* L.progress "check nonnullness for %a in %a@." Procname.pp (Procname.Java mthd) Procname.Set.pp callees ; *)
    Procname.Set.for_all (Program.is_constant_proc program) callees


let is_almost_constant vals =
  match AbsVal.is_singleton_or_more vals with
  | Empty ->
      true
  | Singleton v ->
      Val.is_concrete v && Val.is_primitive v
  | _ ->
      false


let rec resolve_symbol ~caller_astate ~callee_astate param_to_absval symbol : AbsVal.t =
  match symbol with
  | Symbol.Abstract _ ->
      top_value
  | Symbol.Path (base, accs) | Symbol.Last (base, accs) -> (
    match (base, List.rev accs) with
    | Symbol.Param _, Symbol.Field fn :: remain ->
        let base_value =
          resolve_symbol ~caller_astate ~callee_astate param_to_absval
            (Symbol.Path (base, List.rev remain))
        in
        let locs = Loc.append_fields ~fn (Loc.from_vals base_value) in
        read_locs caller_astate locs
    | Symbol.Param _, Symbol.Index _ :: remain ->
        let base_value =
          resolve_symbol ~caller_astate ~callee_astate param_to_absval
            (Symbol.Path (base, List.rev remain))
        in
        let locs = Loc.append_indexs (Loc.from_vals base_value) in
        read_locs caller_astate locs
    | Symbol.Param (_, pv), [] ->
        param_to_absval pv
    | Symbol.Global _, _ ->
        AbsVal.singleton (Val.VSymbol (Symbol.Path (base, accs))) )


let resolve_val ~caller_astate ~callee_astate formals actual_values ret_value =
  let resolve_symval = function
    | Val.VSymbol s ->
        let param_to_absval pv =
          List.fold2_exn formals actual_values ~init:AbsVal.bottom ~f:(fun acc (fv, _) value ->
              if Pvar.equal fv pv then value else acc )
        in
        resolve_symbol ~caller_astate ~callee_astate param_to_absval s
    | v when Val.is_primitive v ->
        ret_value
    | _ ->
        top_value
  in
  AbsVal.fold (AbsVal.join <<< resolve_symval) ret_value AbsVal.bottom


let get_return_val memory actual_values callee = AbsVal.top

let rec eval_astexp memory (ae : AE.t) =
  let eval_astexp = eval_astexp in
  let read_locs = read_locs memory in
  match ae with
  | Var (pv, _) when Pvar.is_this pv ->
      AbsVal.singleton nonnull_absval
  | Var (pv, _) ->
      read_locs (Loc.of_pvar pv |> Loc.Set.singleton)
  | Literal (Integer intlit) ->
      Val.make_int intlit |> AbsVal.singleton
  | Literal NULL ->
      Val.null |> AbsVal.singleton
  | Literal (Boolean true) ->
      Val.one |> AbsVal.singleton
  | Literal (Boolean false) ->
      Val.zero |> AbsVal.singleton
  | Literal (Float f) ->
      Val.make_float f |> AbsVal.singleton
  | Literal (String _) when AE.equal ae AE.mask_token ->
      AbsVal.top
  | Literal (String str) ->
      Val.make_string str |> AbsVal.singleton
  | Literal (Class name) ->
      let class_name = Ident.name_to_string name in
      Val.make_injective BasicDom.Models.cls [Val.make_string class_name] |> AbsVal.singleton
  | FieldAccess {base= DynamicAccess base_e; field_hole= Filled fn} ->
      let base_locs = eval_astexp memory base_e |> Loc.from_vals in
      Loc.append_fields base_locs ~fn |> read_locs
  | FieldAccess {base= StaticAccess (Filled _); field_hole= Filled _} ->
      AbsVal.singleton nonnull_absval
  | ArrayAccess {arrexp} ->
      let base_locs = eval_astexp memory arrexp |> Loc.from_vals in
      Loc.append_indexs base_locs |> read_locs
  | Cast (_, ae) ->
      eval_astexp memory ae
  | NewArray _ ->
      AbsVal.singleton (Val.make_allocsite InstrNode.dummy)
  | MethodCall {base= DynamicAccess base_e; mthd_hole= Filled mthd; args_hole= Some [arg]}
    when String.equal "equals" (AE.Method.get_method mthd) ->
      if AE.equal base_e arg then AbsVal.singleton Val.one
      else if Typ.equal (AE.typeof base_e) (AE.typeof arg) then AbsVal.top_primitive
      else AbsVal.singleton Val.zero
  | MethodCall {base= DynamicAccess base; mthd_hole= Filled mthd; args_hole= Some args}
    when is_nonnull_mthd (AE.typeof base) mthd args ->
      AbsVal.singleton nonnull_absval
  | MethodCall {base= StaticAccess (Filled baseClass); mthd_hole= Filled mthd; args_hole= Some args}
    when is_nonnull_mthd (Typ.mk_struct baseClass) mthd args ->
      AbsVal.singleton nonnull_absval
  | MethodCall {base= DynamicAccess _; mthd_hole= Filled _; args_hole= Some _} ->
      AbsVal.top_primitive
  | MethodCall {base= StaticAccess (Filled _); mthd_hole= Filled mthd; args_hole= Some []} ->
      let cls = AE.Method.get_class_type_name mthd in
      let gvar = Pvar.mk_global (Mangled.from_string (Typ.Name.name cls)) in
      let callee_name = AE.Method.get_method mthd in
      AbsVal.singleton (Val.VSymbol (Symbol.make_global gvar (Fieldname.make cls callee_name)))
  | MethodCall {base= StaticAccess (Filled _); mthd_hole= Filled _; args_hole= Some _} ->
      AbsVal.top
  | Unary (Unop.LNot, ae) ->
      let bvalues = eval_astexp memory ae in
      let true_or_empty =
        if is_sat memory (bvalues, AbsVal.singleton Val.one, Binop.Eq, InstrNode.dummy) then
          AbsVal.singleton Val.zero
        else AbsVal.empty
      in
      let false_or_empty =
        if is_sat memory (bvalues, AbsVal.singleton Val.zero, Binop.Eq, InstrNode.dummy) then
          AbsVal.singleton Val.one
        else AbsVal.empty
      in
      AbsVal.join true_or_empty false_or_empty
  | Binary (binop, ae1, ae2) ->
      let v1 = eval_astexp memory ae1 in
      let v2 = eval_astexp memory ae2 in
      let true_or_empty =
        if is_sat memory (v1, v2, binop, InstrNode.dummy) then AbsVal.singleton Val.one
        else AbsVal.empty
      in
      let false_or_empty =
        match Binop.negate binop with
        | Some binop' when not (is_sat memory (v1, v2, binop', InstrNode.dummy)) ->
            AbsVal.empty
        | _ ->
            AbsVal.singleton Val.zero
      in
      AbsVal.join true_or_empty false_or_empty
  | Ternary (bexp, ae1, ae2) ->
      let bvalues = eval_astexp memory bexp in
      let v1 = eval_astexp memory ae1 in
      let v2 = eval_astexp memory ae2 in
      let true_or_empty =
        if is_sat memory (bvalues, AbsVal.singleton Val.one, Binop.Eq, InstrNode.dummy) then v1
        else AbsVal.empty
      in
      let false_or_empty =
        if is_sat memory (bvalues, AbsVal.singleton Val.zero, Binop.Eq, InstrNode.dummy) then v2
        else AbsVal.empty
      in
      AbsVal.join true_or_empty false_or_empty
  | Hole _ | FieldAccess _ | MethodCall _ ->
      AbsVal.top
  | Unary _ ->
      AbsVal.top_primitive


let check_expectation memory =
  let eval_astexp = eval_astexp in
  function
  | Equal (ae1, ae2) ->
      is_sat memory (eval_astexp memory ae1, eval_astexp memory ae2, Binop.Eq, InstrNode.dummy)
  | NotEqual (ae1, ae2) ->
      is_sat memory (eval_astexp memory ae1, eval_astexp memory ae2, Binop.Ne, InstrNode.dummy)


let check_always_null memory (ae : ASTExp.t) =
  let rec f : AE.t -> AE.t list = function
    | FieldAccess {base= StaticAccess _} ->
        []
    | FieldAccess {base= DynamicAccess e} ->
        e :: f e
    | MethodCall {base= StaticAccess _; args_hole= Some args} ->
        List.concat_map args ~f
    | MethodCall {base= DynamicAccess e; args_hole= Some args} ->
        e :: List.concat_map (e :: args) ~f
    | ArrayAccess {arrexp; index} ->
        arrexp :: f index
    | Unary (_, e) ->
        f e
    | Cast (_, e) ->
        f e
    | NewArray _ ->
        []
    | Binary (_, e1, e2) ->
        List.concat_map [e1; e2] ~f
    | Ternary (e1, e2, e3) ->
        List.concat_map [e1; e2; e3] ~f
    | Hole _ | MethodCall _ ->
        []
    | Var _ | Literal _ ->
        []
  in
  (* TODO: it is not sufficient to look up memory-only *)
  let is_always_null e = NotEqual (e, AE.null) |> check_expectation memory |> not in
  let base_expressions = f ae in
  List.exists base_expressions ~f:is_always_null


let check_redundancy memory (ae : AE.t) =
  let is_redundant (ae : AE.t) =
    eval_astexp memory ae |> is_almost_constant
    ||
    match ae with
    | Binary ((Binop.Eq | Binop.Ne), Literal _, _) ->
        (* TODO: remove it if implemented in enumerator *)
        true
    | Binary ((Binop.Eq | Binop.Ne), lhs, rhs)
      when Typ.equal Typ.boolean (AE.typeof lhs |> strip_ptr)
           && Typ.equal Typ.boolean (AE.typeof rhs |> strip_ptr) ->
        (* TODO: remove it if implemented in enumerator *)
        true
    | FieldAccess {field_hole= Filled fn} when Program.has_syntactic_getter fn ->
        true
    | FieldAccess {base= StaticAccess (Filled cls); field_hole= Filled fn}
      when not (Typ.Name.equal cls (Fieldname.get_class_name fn)) ->
        (* TODO: remove it if implemented in enumerator *)
        true
    | FieldAccess {base= StaticAccess _; field_hole= Filled fn} -> (
      match Program.get_field_typ_opt fn with Some Typ.{desc= Tint IBool} -> true | _ -> false )
    | MethodCall {base= StaticAccess _; args_hole= Some [Literal _]}
    | MethodCall {base= StaticAccess _; args_hole= Some [FieldAccess {base= StaticAccess _}]}
    | MethodCall
        {base= DynamicAccess (FieldAccess {base= StaticAccess _}); args_hole= Some [Literal _]}
    | MethodCall
        { base= DynamicAccess (FieldAccess {base= StaticAccess _})
        ; args_hole= Some [FieldAccess {base= StaticAccess _}] }
    | MethodCall {base= DynamicAccess (FieldAccess {base= StaticAccess _}); args_hole= Some []} ->
        (* C.foo(null), C.f.foo(), C.f.foo(null) are almost constants *)
        true
    | MethodCall {mthd_hole= Filled mthd}
      when Fl4aprModels.implements_interfaces ["java.lang.Enum"]
             (AE.Method.get_class_type_name mthd)
           && Program.is_undef_proc (Program.from_marshal ()) (Procname.Java mthd) ->
        true
    | MethodCall {mthd_hole= Filled mthd; args_hole= Some []}
      when List.mem ~equal:String.equal ["hashCode"] (AE.Method.get_method mthd) ->
        true
    | MethodCall {base= DynamicAccess (Var (pv, _)); mthd_hole= Filled mthd; args_hole= Some []}
      when List.mem ~equal:String.equal ["getClass"; "toString"] (AE.Method.get_method mthd)
           && Pvar.is_this pv ->
        (* this.getClass(), this.toString() *)
        true
    | MethodCall {base= DynamicAccess base; mthd_hole= Filled mthd}
      when is_constant_mthd (AE.typeof base) mthd ->
        true
    | MethodCall {base= StaticAccess (Filled baseClass); mthd_hole= Filled mthd}
      when is_constant_mthd (Typ.mk_struct baseClass) mthd ->
        true
    | _ ->
        false
  in
  let rec collect_non_literal_exprs : AE.t -> AE.t list = function
    | FieldAccess {base= DynamicAccess e} as ae ->
        ae :: e :: collect_non_literal_exprs e
    | FieldAccess {base= StaticAccess _} as ae ->
        [ae]
    | MethodCall {base= DynamicAccess e; args_hole= Some args} as ae ->
        ae :: List.concat_map (e :: args) ~f:collect_non_literal_exprs
    | MethodCall {base= StaticAccess _; args_hole= Some args} as ae ->
        ae :: List.concat_map args ~f:collect_non_literal_exprs
    | ArrayAccess {arrexp; index} as ae ->
        ae :: arrexp :: collect_non_literal_exprs index
    | Unary (_, e) as ae ->
        ae :: collect_non_literal_exprs e
    | Cast (_, e) ->
        collect_non_literal_exprs e
    | NewArray _ as ae ->
        [ae]
    | Binary (_, e1, e2) as e ->
        e :: List.concat_map [e1; e2] ~f:collect_non_literal_exprs
    | Ternary (e1, e2, e3) as e ->
        e :: List.concat_map [e1; e2; e3] ~f:collect_non_literal_exprs
    | Hole _ | MethodCall _ ->
        []
    | Var _ as e ->
        [e]
    | Literal _ ->
        []
  in
  let non_literal_exprs = collect_non_literal_exprs ae in
  List.for_all non_literal_exprs ~f:(not <<< is_redundant)


type result = SAT | UNSAT | OutOfScope | Redundant [@@deriving yojson]

let pp_result fmt =
  (function SAT -> "SAT" | UNSAT -> "UNSAT" | OutOfScope -> "OOS" | Redundant -> "Redundant")
  >>> F.fprintf fmt "%s"


let astate_cache = ref InstrNode.Map.empty

let filter fault patch =
  let faulty_node = Fault.get_location_node fault.Fault.loc in
  let proc = Patch.(patch.procname) in
  let astate =
    match InstrNode.Map.find_opt faulty_node !astate_cache with
    | Some astate ->
        astate
    | None ->
        let astate =
          try
            Utils.with_file_in
              (F.asprintf "%s/%a" Config.sprint_invmap_dir InstrNode.pp_id faulty_node)
              ~f:Marshal.from_channel
          with _ ->
            L.progress "could not find marshal from %s/%a@." Config.sprint_invmap_dir
              InstrNode.pp_id faulty_node ;
            Domain.bottom
        in
        astate_cache := InstrNode.Map.add faulty_node astate !astate_cache ;
        astate
  in
  let failing_contexts = DynInfo.ctxs_of_proc_visited proc in
  let rule_filter_unsatisfiable () =
    List.for_all (generate_expectations failing_contexts patch) ~f:(check_expectation astate)
    && List.for_all (Patch.get_expressions patch) ~f:(not <<< check_always_null astate)
  in
  let rule_filter_redundant () =
    List.for_all (Patch.get_expressions patch) ~f:(check_redundancy astate)
  in
  try
    if not (rule_filter_unsatisfiable ()) then UNSAT
    else if not (rule_filter_redundant ()) then Redundant
    else SAT
  with OutOfScopeExn -> OutOfScope


let print name msg =
  let oc = Out_channel.create ~append:true name in
  Out_channel.output_string oc msg ;
  Out_channel.close oc


let filter_patches fault patches =
  (* L.progress "-- Start to filter %d patches@." (List.length patches) ; *)
  if List.length patches > 10000000 then (
    L.progress "Too many patches to filter : %d" (List.length patches) ;
    L.exit 21 ) ;
  let sats, unsats, reduns, out_of_scopes =
    List.fold ~init:([], [], [], []) patches ~f:(fun (sats, unsats, reduns, oos) patch ->
        match Profiler.pick "SATCheck" filter fault patch with
        | SAT ->
            (patch :: sats, unsats, reduns, oos)
        | UNSAT ->
            (sats, patch :: unsats, reduns, oos)
        | Redundant ->
            (sats, unsats, patch :: reduns, oos)
        | OutOfScope ->
            (sats, unsats, reduns, patch :: oos) )
  in
  Profiler.report () ;
  if List.length sats > 100000 then (
    L.progress "Too many SAT patches : %d" (List.length patches) ;
    L.exit 21 ) ;
  L.progress "# Patches changed: from %d to (SAT %d, UNSAT %d, OOS %d REDUNS %d)@."
    (List.length patches) (List.length sats) (List.length unsats) (List.length out_of_scopes)
    (List.length reduns) ;
  print "patches_sat" (F.asprintf "%a" (Pp.seq Patch.pp ~sep:"\n") sats) ;
  print "patches_unsat" (F.asprintf "%a" (Pp.seq Patch.pp ~sep:"\n") unsats) ;
  print "patches_reduns" (F.asprintf "%a" (Pp.seq Patch.pp ~sep:"\n") reduns) ;
  print "patches_oos" (F.asprintf "%a" (Pp.seq Patch.pp ~sep:"\n") out_of_scopes) ;
  sats
