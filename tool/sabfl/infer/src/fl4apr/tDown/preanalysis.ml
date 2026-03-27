open! IStd
open! Vocab
module F = Format
module L = Logging
module Contexts = FiptsAnalysisDomain.Contexts
module Context = FiptsAnalysisDomain.Context
module AbsConst = Program.AbsConst

exception PreanalysisError of string

let syntactic_callees program instr_node ~allow_dynamic_only =
  let callees =
    Program.callees_of_instr_node program instr_node
    |> List.filter ~f:(not <<< Program.is_undef_proc program)
  in
  if Int.equal (List.length callees) 1 || not allow_dynamic_only then callees else []


let callees_by_dyninfo program instr_node ~allow_dynamic_only =
  let proc = InstrNode.get_proc_name instr_node in
  match InstrNode.get_instr instr_node with
  | Sil.Call (_, Const (Cfun callee), _, _, _) ->
      let ctxs = DynInfo.ctxs_of_proc_visited proc in
      let callee_procs = DynInfo.get_class_info ctxs instr_node |> Program.resolve_methods callee in
      let callee_procs =
        if List.is_empty callee_procs then (
          L.debug L.Analysis L.Quiet "[WARNING]: no dyncallee for %a@." InstrNode.pp instr_node ;
          syntactic_callees program instr_node ~allow_dynamic_only )
        else callee_procs
      in
      List.iter ~f:(Program.add_call_edge program instr_node) callee_procs ;
      Procname.Set.of_list callee_procs
  | _ ->
      Procname.Set.empty


let callees_by_memory memory program instr_node =
  let proc = InstrNode.get_proc_name instr_node in
  match InstrNode.get_instr instr_node with
  | Sil.Call (_, Const (Cfun callee), arg_typs, _, _) -> (
    match Fl4aprModels.dispatch callee (List.map ~f:snd arg_typs) with
    | Some (MConcurrent Fl4aprModels.Concurrent.Submit) ->
        let callee_procs =
          FiptsAnalysisModels.Concurrent.dispatch_callable proc Context.dummy arg_typs memory
        in
        Procname.Set.iter (Program.add_call_edge program instr_node) callee_procs ;
        callee_procs
    | Some (MConcurrent Fl4aprModels.Concurrent.Start) ->
        let callee_procs =
          FiptsAnalysisModels.Concurrent.dispatch_runnable proc Context.dummy arg_typs memory
        in
        Procname.Set.iter (Program.add_call_edge program instr_node) callee_procs ;
        callee_procs
    | _ ->
        let callee_procs =
          if FiptsAnalysisDomain.is_bottom memory then
            Program.callees_of_instr_node program instr_node
          else
            FiptsAnalysis.callees_of_instr program memory proc Context.dummy instr_node
            |> BasicDom.PowProc.elements
        in
        let callee_procs =
          if List.is_empty callee_procs then (
            L.debug L.Analysis L.Quiet "[WARNING]: no callee for %a@." InstrNode.pp instr_node ;
            syntactic_callees program instr_node ~allow_dynamic_only:true )
          else callee_procs
        in
        List.iter ~f:(Program.add_call_edge program instr_node) callee_procs ;
        Procname.Set.of_list callee_procs )
  | _ ->
      Procname.Set.empty


let draw_callgraph ~reset ~entries compute_callees program =
  let new_program = if reset then Program.reset_cg program else program in
  let rec draw worklist donelist =
    if Procname.Set.is_empty worklist then ()
    else
      let work = Procname.Set.choose worklist in
      let rest = Procname.Set.remove work worklist in
      let inodes = Program.get_nodes program work in
      let inodes =
        if Program.is_entry program work then
          let ctxs = DynInfo.ctxs_of_proc_visited work in
          Contexts.fold
            (fun ctx acc ->
              match ctx with
              | Context.Empty testClass ->
                  InterNode.of_pnode
                    (Program.node_for_junit_premethods program testClass
                       ~clinits:!FiptsAnalysis._clinits work )
                  :: acc
              | _ ->
                  L.(die InternalError)
                    "Invalid context for entry procedure %a (Context %a)" Procname.pp work
                    Context.pp ctx )
            ctxs inodes
        else inodes
      in
      let callees =
        List.fold inodes ~init:Procname.Set.empty ~f:(fun acc inode ->
            let instrs = InterNode.get_instrs inode in
            Instrs.fold instrs ~init:acc ~f:(fun acc instr ->
                let instr_node = InstrNode.{inode; instr} in
                compute_callees new_program instr_node |> Procname.Set.union acc ) )
      in
      let next_donelist = Procname.Set.add work donelist in
      let next_worklist =
        Procname.Set.diff callees next_donelist
        |> Procname.Set.filter (not <<< Program.is_undef_proc program)
        |> Procname.Set.union rest
      in
      draw next_worklist next_donelist
  in
  draw entries Procname.Set.empty ;
  new_program


let add_important_param_typs program memory =
  let all_procs = Program.all_procs program in
  Procname.Set.iter
    (fun proc ->
      let pdesc = Program.pdesc_of program proc in
      let formals = Procdesc.get_pvar_formals pdesc in
      let formal_locs =
        List.concat_map formals ~f:(fun (pv, typ) ->
            let pv_locs =
              FiptsAnalysisDomain.ptsto_of_locs memory
                (BasicDom.Loc.of_pvar ~ctx:Context.dummy pv |> BasicDom.PowLoc.singleton)
            in
            let pv_locs_exp = (pv_locs, Exp.Lvar pv) in
            match Typ.name (strip_ptr typ) with
            | Some name when Pvar.is_this pv -> (
              match Program.Class.lookup program name with
              | Some Struct.{fields} ->
                  pv_locs_exp
                  :: List.map fields ~f:(fun (fn, fn_typ, _) ->
                         let exp = Exp.Lfield (Exp.Lvar pv, fn, fn_typ) in
                         let locs = BasicDom.PowLoc.append_fields pv_locs ~fn in
                         let fn_ptsto_locs = FiptsAnalysisDomain.ptsto_of_locs memory locs in
                         (fn_ptsto_locs, exp) )
              | None ->
                  [pv_locs_exp] )
            | _ ->
                [pv_locs_exp] )
      in
      let important_param_typs =
        List.fold formal_locs
          ~init:(Exp.Var (Ident.create_none ()), Typ.Name.Set.empty)
          ~f:(fun (acc_param, acc_typs) (locs, exp) ->
            let typs =
              BasicDom.PowLoc.fold
                (fun loc acc ->
                  match
                    strip_ptr (FiptsAnalysisDomain.type_of_loc memory loc |> BasicDom.AbsTyp.typ_of)
                  with
                  | Typ.{desc= Tstruct name} ->
                      Typ.Name.Set.add name acc
                  | _ ->
                      acc )
                locs Typ.Name.Set.empty
            in
            if Typ.Name.Set.cardinal acc_typs < Typ.Name.Set.cardinal typs then (exp, typs)
            else (acc_param, acc_typs) )
      in
      Program.add_param_typs program proc important_param_typs )
    all_procs ;
  program


let compute_return_values ~get_summary program memory =
  let open FiptsAnalysisDomain in
  let open BasicDom in
  let semantically_nonnulls =
    Mem.fold
      (fun l v acc ->
        match l with
        | Loc.Pvar (_, pv) when Pvar.is_return pv -> (
          match Pvar.get_declaring_function pv with
          | Some (Procname.Java mthd) when not (Typ.is_void (Procname.Java.get_return_typ mthd)) ->
              let locs = Val.get_locs v in
              if not (PowLoc.exists Loc.is_null locs) then
                Procname.Map.add (Procname.Java mthd) Program.AbsConst.NonNull acc
              else acc
          | _ ->
              acc )
        | _ ->
            acc )
      memory.mem Procname.Map.empty
  in
  let all_procs = Program.all_procs program in
  let return_values =
    Procname.Set.fold
      (fun callee acc ->
        let v = get_summary callee in
        if AbsConst.is_nonconst v then acc else Procname.Map.add callee v acc )
      all_procs semantically_nonnulls
  in
  let msg = F.asprintf "%a" (Procname.Map.pp ~pp_value:Program.AbsConst.pp) return_values in
  print_to_file ~dirname:None ~msg ~filename:"return_values" ;
  Program.set_return_values program return_values


module ParamField = Program.ParamField
module ParamFields = Program.ParamFields
module SideEffects = Program.SideEffects

let compute_side_effects_of_proc program proc side_effects =
  let pdesc = Program.pdesc_of program proc in
  let params = List.mapi (Procdesc.get_pvar_formals pdesc) ~f:(fun i (pv, _) -> (i, pv)) in
  let rec param_field_of_ae : ASTExp.t -> ParamField.t option = function
    | FieldAccess {base= DynamicAccess (Var (pv, _)); field_hole= Filled fn} ->
        List.find_map params ~f:(fun (i, pv') -> if Pvar.equal pv pv' then Some (i, fn) else None)
    | FieldAccess {base= DynamicAccess ae} ->
        param_field_of_ae ae
    | ArrayAccess {arrexp} ->
        param_field_of_ae arrexp
    | _ ->
        None
  in
  let param_field_of e =
    match ASTExp.from_IR_exp_opt pdesc e with
    | Some (ASTExp.FieldAccess _ as ae) ->
        param_field_of_ae ae
    | _ ->
        None
  in
  let param_field_of_with_field e ~fn =
    match ASTExp.from_IR_exp_opt pdesc e with
    | Some (ASTExp.Var _ as ae) ->
        param_field_of_ae (ASTExp.FieldAccess {base= DynamicAccess ae; field_hole= Filled fn})
    | Some (ASTExp.FieldAccess _ as ae) ->
        param_field_of_ae ae
    | _ ->
        None
  in
  let nodes = Procdesc.get_nodes pdesc in
  let compute_side_effect_of_call callee (this_exp, this_typ) =
    if String.is_prefix (Procname.get_method callee) ~prefix:"set" then
      let fieldname =
        String.chop_prefix_exn (Procname.get_method callee) ~prefix:"set" |> String.uncapitalize
      in
      match Typ.(this_typ.desc) with
      | Tptr ({desc= Tstruct name}, _) ->
          let fn = Fieldname.make name fieldname in
          param_field_of_with_field this_exp ~fn
      | _ ->
          param_field_of this_exp
    else param_field_of this_exp
  in
  let side_effect_of_proc =
    List.fold nodes ~init:ParamFields.empty ~f:(fun acc node ->
        Instrs.fold (Procdesc.Node.get_instrs node) ~init:acc ~f:(fun acc instr ->
            let instr_node = InstrNode.of_pnode node instr in
            match instr with
            | Sil.Store {e1= Lfield (e, fn, _)} -> (
              match param_field_of_with_field e ~fn with
              | Some param_field ->
                  ParamFields.add param_field acc
              | None ->
                  acc )
            | Sil.Call (_, Const (Cfun callee), (this_exp, this_typ) :: _, _, _)
              when Program.is_library_call program instr_node -> (
              match compute_side_effect_of_call callee (this_exp, this_typ) with
              | Some param_field ->
                  ParamFields.add param_field acc
              | None ->
                  acc )
            | Sil.Call (_, _, arg_typs, _, _) ->
                let callees = Program.callees_of_instr_node program instr_node in
                List.fold callees ~init:acc ~f:(fun acc callee ->
                    ParamFields.fold
                      (fun (i, fn) acc ->
                        match List.nth_exn arg_typs i |> fst |> param_field_of_with_field ~fn with
                        | Some param_field ->
                            ParamFields.add param_field acc
                        | None ->
                            acc )
                      (SideEffects.find callee side_effects)
                      acc )
            | _ ->
                acc ) )
  in
  if ParamFields.is_empty side_effect_of_proc then side_effects
  else SideEffects.add proc side_effect_of_proc side_effects


let compute_side_effects program =
  let all_procs =
    Program.all_procs program |> Procname.Set.filter (not <<< Program.is_undef_proc program)
  in
  let rec compute_all acc =
    let next =
      Procname.Set.fold (fun proc -> compute_side_effects_of_proc program proc) all_procs acc
    in
    if SideEffects.leq ~lhs:next ~rhs:acc then acc else compute_all next
  in
  let results = compute_all SideEffects.empty in
  let msg = F.asprintf "%a" SideEffects.pp results in
  print_to_file ~dirname:None ~msg ~filename:"side-effetcs" ;
  Program.set_side_effects program results


let get_program_by_pointer_analysis program ~entries =
  L.debug L.Analysis L.Quiet "- Entries of analysis : @[%a@].@." Procname.Set.pp entries ;
  L.progress "- doing flow-insensitive pointer analysis ...@." ;
  let mem = FiptsAnalysis.do_pointer_analysis ~entries program in
  if Config.debug_level_analysis > 0 then (
    L.progress "- printing result memories ...@." ;
    Utils.with_file_out (Config.results_dir ^/ "memory.results") ~f:(fun oc ->
        let fmt = F.formatter_of_out_channel oc in
        F.fprintf fmt "%a" FiptsAnalysisDomain.pp mem ) ) ;
  let mem_insen = FiptsAnalysisDomain.insensitive_memory mem in
  L.progress "- Drawing call graph ... @." ;
  (* let program = draw_callgraph ~entries FiptsAnalysisDomain.bottom program in *)
  draw_callgraph ~reset:true ~entries (callees_by_memory mem_insen) program
  |> draw_callgraph ~reset:false ~entries (callees_by_dyninfo ~allow_dynamic_only:true)


let get_entries program =
  let entries = Program.get_entries program in
  if List.is_empty entries then
    let is_model pid = Program.is_undef_proc program pid in
    List.fold
      (Program.all_procs program |> Procname.Set.elements)
      ~init:Procname.Set.empty
      ~f:(fun acc pid ->
        if (not (is_model pid)) && List.is_empty (Program.callers_of_proc program pid) then
          Procname.Set.add pid acc
        else acc )
  else
    let clinits =
      Program.all_procs program
      |> Procname.Set.filter Procname.is_java_class_initializer
      |> Procname.Set.filter (fun proc ->
             not (Contexts.is_empty (DynInfo.ctxs_of_proc_visited proc)) )
      |> Procname.Set.filter (not <<< Program.is_undef_proc program)
    in
    Procname.Set.union (Procname.Set.of_list entries) clinits


let is_sus_procs_unreachable program entries sus_procs =
  let reachables = Program.cg_reachables_of program entries in
  let sus_procs =
    (* filter out procs not well supported by callgraph *)
    Procname.Set.filter
      (fun proc ->
        (not (Procname.is_java_class_initializer proc))
        && not (Procname.get_method proc |> String.equal "toString") )
      sus_procs
  in
  L.debug L.Analysis L.Quiet "- Reachables of analysis : @[%a@].@." Procname.Set.pp reachables ;
  L.debug L.Analysis L.Quiet "- Suspected procedures : @[%a@].@." Procname.Set.pp sus_procs ;
  not (Procname.Set.subset sus_procs reachables)


let analyze sus_procs program =
  (* to configure unreachable procedures *)
  let program = Program.construct_cg program in
  let _ =
    let dyninfo = DynInfo.parse_dyninfo program in
    print_to_file ~dirname:None
      ~msg:(F.asprintf "%a" DynInfo.pp dyninfo)
      ~filename:"dyninfo.results"
  in
  let entries = get_entries program in
  if is_sus_procs_unreachable program entries sus_procs then
    print_to_file ~dirname:None ~msg:"Unreachable" ~filename:Config.sprint_preanalysis_result
  else print_to_file ~dirname:None ~msg:"Default" ~filename:Config.sprint_preanalysis_result ;
  let program_by_analysis = get_program_by_pointer_analysis program ~entries in
  Program.print_callgraph program_by_analysis "callgraph_analyzed.dot" ;
  let program =
    if is_sus_procs_unreachable program_by_analysis entries sus_procs then program
    else (
      print_to_file ~dirname:None ~msg:"Analysis" ~filename:Config.sprint_preanalysis_result ;
      program_by_analysis )
  in
  let program = Program.remove_cfg_if_no_cg program in
  (* let program = add_important_param_typs program mem_insen in *)
  Program.print_param_typs program "important_param_typs" ;
  Program.to_marshal Program.marshalled_path program ;
  Program.print_callgraph program "callgraph_sliced.dot" ;
  program
