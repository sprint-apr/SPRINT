open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
module Symbol = SymDom.Symbol
module Loc = SymDom.SymLoc
module Val = SymDom.SymVal
module AbsVal = SymDom.AbsVal
module DiffVal = Domain.DiffVal
module Disjunct = Domain.Disjunct
module SymDiff = Domain.SymDiff

type t = Domain.t list * Domain.t list

type analysis_data = Procname.t -> t option

let get_disjuncts : t -> Domain.t list = fst

let get_local_disjuncts : t -> Domain.t list = snd

let pp f (t : t) =
  let pp_elements f disjuncts =
    List.iteri disjuncts ~f:(fun i disjunct ->
        if (not (Domain.is_exceptional disjunct)) || Config.debug_level_analysis > 3 then
          F.fprintf f "#%d: @[%a@]@;" i Domain.pp disjunct )
  in
  let disjuncts = get_disjuncts t in
  F.fprintf f "%d disjuncts:@.%a@." (List.length disjuncts) pp_elements disjuncts


type get_summary = Procname.t -> t option

let empty : t = ([], [])

let to_summary proc_desc disjuncts =
  let disjuncts = List.filter disjuncts ~f:Domain.is_satisfiable in
  Verify.check_summary proc_desc disjuncts ;
  (* filter invalid states *)
  (* L.(debug Analysis Quiet)
       "@.---- Analysis time result of %a ----@." Procname.pp (Procdesc.get_proc_name proc_desc) ;
     debug_time_finalize () ; *)
  let proc = Procdesc.get_proc_name proc_desc in
  let local_disjuncts = List.filter disjuncts ~f:(not <<< Domain.is_conditional) in
  let program = Program.from_marshal () in
  let filter_trivial_disjuncts disjuncts =
    if Config.sprint_exnchecker || Config.sprint_no_test || Config.sprint_method_level then
      disjuncts
    else if Program.is_entry program proc then disjuncts
    else
      List.filter_map disjuncts ~f:(fun astate ->
          match (Domain.(astate.last_org), proc) with
          | Past _, _ | Original, _ ->
              Some astate
          | Current _, _ when Domain.(Mem.is_bottom astate.mem) ->
              None
          | Current _, Java mthd ->
              Heuristics.filter_trivial_diff mthd astate
          | Current _, _ ->
              Some astate )
  in
  let print_debug inter_disjuncts =
    let exceptional_abs_patches, normal_abs_patches =
      let exceptionals, normals = List.partition_tf ~f:Domain.is_exceptional inter_disjuncts in
      ( List.fold exceptionals ~init:Fault.Set.empty ~f:(fun acc Domain.{abs_patches} ->
            match abs_patches with
            | Some abs_patches ->
                Fault.Set.union abs_patches acc
            | None ->
                acc )
      , List.fold normals ~init:Fault.Set.empty ~f:(fun acc Domain.{abs_patches} ->
            match abs_patches with
            | Some abs_patches ->
                Fault.Set.union abs_patches acc
            | None ->
                acc ) )
    in
    if Fault.Set.is_empty exceptional_abs_patches && Fault.Set.is_empty normal_abs_patches then
      L.debug L.Analysis L.Verbose "No abs_patches analyzed: at %a@." Procname.pp proc
    else
      L.progress " - abs_patches analyzed: (%d, %d) at %a@."
        (Fault.Set.cardinal normal_abs_patches)
        (Fault.Set.cardinal exceptional_abs_patches)
        Procname.pp proc
  in
  let print_sat_equal_abs_patches local_disjuncts =
    (* fid -> 2^sid *)
    let abs_patches_list =
      List.filter_map local_disjuncts ~f:(fun astate ->
          match Domain.(astate.abs_patches) with
          | Some abs_patches ->
              let abs_patches =
                Fault.Set.filter (Procname.equal proc <<< Fault.get_proc_name) abs_patches
              in
              if Fault.Set.is_empty abs_patches then None else Some abs_patches
          | None ->
              None )
    in
    let all_abs_patches = List.fold abs_patches_list ~init:Fault.Set.empty ~f:Fault.Set.union in
    let abs_patches_set =
      List.fold abs_patches_list
        ~init:[Fault.Set.elements all_abs_patches]
        ~f:(fun acc abs_patches ->
          let partition_by_abs_patches =
            List.map acc ~f:(fun abs_patches' ->
                List.partition_tf abs_patches' ~f:(fun fault -> Fault.Set.mem fault abs_patches) )
          in
          let inner_abs_patches, outer_abs_patches = List.unzip partition_by_abs_patches in
          List.filter_map (outer_abs_patches @ inner_abs_patches) ~f:(fun abs_patches ->
              if List.is_empty abs_patches then None else Some abs_patches ) )
      |> List.map ~f:Fault.Set.of_list
      (* |> FSetSet.of_list *)
    in
    if not (List.is_empty abs_patches_set) then (
      let filename = Procname.to_filename proc in
      print_to_file ~dirname:(Some Config.sprint_sat_equal_abs_patches_dir)
        ~msg:(F.asprintf "%a" (Pp.seq ~sep:"\n" Fault.Set.pp) abs_patches_set)
        ~filename:(filename ^ ".txt") ;
      to_marshal ~dirname:(Some Config.sprint_sat_equal_abs_patches_dir) abs_patches_set
        ~filename:(filename ^ ".data") )
  in
  print_sat_equal_abs_patches local_disjuncts ;
  (* L.progress "Analyzed Faults: %a at %a@." Fault.Set.pp all_abs_patches Procname.pp (Procdesc.get_proc_name proc_desc) ; *)
  AnalysisCallbacks.html_debug_new_node_session
    (Procdesc.get_start_node proc_desc)
    ~kind:`ComputePre
    ~pp_name:(fun fmt -> F.fprintf fmt "==== Spec Checker Join ====@.")
    ~f:(fun () ->
      let inter_disjuncts =
        List.map local_disjuncts ~f:(fun astate ->
            L.d_printfln "Before Remove Locals: %a@." Domain.pp_sig astate ;
            let astate =
              Domain.
                { astate with
                  control_deps= ControlDeps.bottom
                ; loc_def= LocDef.empty
                ; id_use= IdUse.empty }
            in
            Domain.remove_unreachables_summary astate proc_desc )
        |> Heuristics.simplify_summaries proc_desc
        |> filter_trivial_disjuncts
      in
      let results = Domain.merge inter_disjuncts in
      L.d_printfln "Merge on summary done" ;
      print_debug results ;
      (results, local_disjuncts) )


let get_only_normals (inter_disjuncts, local_disjuncts) : t =
  let filter = List.filter ~f:Domain.is_original in
  (filter inter_disjuncts, filter local_disjuncts)


(** Symbolic domain *)
module SymResolvedMap = struct
  include PrettyPrintable.MakePPMonoMap (Symbol) (DiffVal)

  let __cache = ref empty

  let __astate = ref Domain.bottom

  let __field_map = ref Domain.LocTable.empty

  let __absloc_map = ref Domain.LocTable.empty

  let __is_org_die = ref `Unknown

  let __astate_with_merged_mem = ref Domain.bottom

  let init astate instr_node ~formals ~actual_values =
    let init_sym_resolved_map =
      List.mapi actual_values ~f:(fun i v -> (i, v))
      |> List.fold2_exn formals ~init:empty ~f:(fun sym_resolved_map (fv, _) (i, diffval) ->
             add (Symbol.of_pvar i fv) diffval sym_resolved_map )
    in
    L.d_printfln
      "[DEBUG]: init sym_resolved_map@. - Formals: %a@.%a@.====================================@."
      (Pp.seq (Pvar.pp Pp.text))
      (List.map ~f:fst formals) pp init_sym_resolved_map ;
    __cache := init_sym_resolved_map ;
    __absloc_map := Domain.LocTable.empty ;
    __astate := astate ;
    __astate_with_merged_mem := Domain.astate_with_merged_mem astate ;
    __is_org_die := Domain.is_dynamic_throw astate instr_node ;
    __field_map := Domain.(compute_field_map !__astate_with_merged_mem.mem)


  let rec compute_reachable_values base_locs done_locs acc_diff_val =
    let open Domain in
    let base_field_locs =
      Loc.Set.fold (fun l -> LocTable.find l !__field_map |> Loc.Set.union) base_locs Loc.Set.empty
    in
    let next_val = read_locs !__astate (base_field_locs, SymDiff.empty) in
    L.d_printfln "next_val of %a(%a): %a@." Loc.Set.pp base_field_locs Loc.Set.pp base_locs
      AbsVal.pp (fst next_val) ;
    let done_locs = Loc.Set.union base_locs done_locs in
    let next_locs = Loc.Set.diff (Loc.from_vals (fst next_val)) done_locs in
    let post_val = DiffVal.union acc_diff_val next_val in
    if DiffVal.equal post_val acc_diff_val then acc_diff_val
    else compute_reachable_values next_locs done_locs post_val


  let rec find symbol : DiffVal.t =
    match (find_opt symbol !__cache, symbol) with
    | Some diffval, _ ->
        diffval
    | None, (Symbol.Path (base, accesses) | Symbol.Last (base, accesses)) ->
        let diffval =
          match (base, List.rev accesses) with
          | Symbol.Global (pv, Symbol.Field fn), [] ->
              Domain.read_loc !__astate (Loc.of_pvar pv |> Loc.append_field ~fn, SymDiff.empty)
          | Symbol.Global (_, Symbol.Index _), [] ->
              L.(die InternalError) "Invalid symbol"
          | Symbol.Param _, [] ->
              L.(die InternalError)
                "Initial Parameter should be initialized before find %a@.%a@." Symbol.pp symbol pp
                !__cache
          | base, Symbol.Field fn :: remain ->
              let base_vals, symdiff = find (Symbol.Path (base, List.rev remain)) in
              let locs = Loc.Set.map (Loc.append_field ~fn) (Loc.from_vals base_vals) in
              let resolved_val, symdiff = Domain.read_locs !__astate (locs, symdiff) in
              (resolved_val, symdiff)
          | base, Symbol.Index _ :: remain ->
              let base_vals, symdiff = find (Symbol.Path (base, List.rev remain)) in
              let locs = Loc.append_indexs (Loc.from_vals base_vals) in
              let resolved_val, symdiff = Domain.read_locs !__astate (locs, symdiff) in
              (resolved_val, symdiff)
        in
        L.d_printfln "[DEBUG]: resolve %a to %a" Symbol.pp symbol DiffVal.pp diffval ;
        __cache := add symbol diffval !__cache ;
        diffval
    | None, Symbol.Abstract (base, accesses, access) ->
        let last_symbol = Symbol.Last (base, accesses) in
        let base_loc = Loc.SymHeap (VSymbol last_symbol) in
        let diffval_base = find last_symbol in
        let diffval =
          let symloc = Loc.append_access access base_loc in
          let base_locs = Loc.from_vals (fst diffval_base) in
          let base_locs_access_appended =
            Loc.Set.map (Loc.append_access access) base_locs
            |> Loc.Set.filter Loc.is_abstract_symloc
          in
          let reachable_locs =
            let reachable_values, _ =
              compute_reachable_values base_locs Loc.Set.empty diffval_base
            in
            let reachable_locs =
              match access with
              | Symbol.Field fn ->
                  Loc.from_vals reachable_values |> Loc.append_fields ~fn
              | Symbol.Index _ ->
                  Loc.from_vals reachable_values |> Loc.append_indexs
            in
            Loc.Set.filter
              (fun l -> Domain.Mem.mem l !__astate_with_merged_mem.mem || Loc.is_abstract_heap l)
              reachable_locs
          in
          let resolved_locs = Loc.Set.union base_locs_access_appended reachable_locs in
          let resolved_locs =
            if Loc.Set.is_empty resolved_locs then (
              L.d_printfln "Resolved locations are empty!!! use abstract heap instead" ;
              Loc.from_vals AbsVal.top )
            else resolved_locs
          in
          __absloc_map := Domain.LocTable.add symloc resolved_locs !__absloc_map ;
          let value, symdiff = Domain.read_locs !__astate (resolved_locs, snd diffval_base) in
          match AbsVal.is_singleton_or_more value with
          | Singleton (Val.VString _) ->
              (AbsVal.singleton Val.top_primitive, symdiff)
          | _ ->
              (value, symdiff)
        in
        L.d_printfln "[DEBUG]: resolve %a to %a" Symbol.pp symbol DiffVal.pp diffval ;
        __cache := add symbol diffval !__cache ;
        diffval


  let rec resolve_val : Val.t -> AbsVal.t = function
    | Val.VSymbol s ->
        fst (find s)
    | VInjFunction (mthd, args) ->
        let args_replaced = List.map args ~f:resolve_val in
        AbsVal.make_injective mthd args_replaced
    | VFunction (mthd, args) ->
        let args_replaced = List.map args ~f:resolve_val in
        AbsVal.make_uninterpret mthd args_replaced
    | VAbsFun (mthd, args) ->
        let args_replaced = List.map args ~f:resolve_val in
        AbsVal.make_absfun mthd args_replaced
    | v ->
        AbsVal.singleton v


  let resolve_vals vals = AbsVal.fold (fun v -> AbsVal.join (resolve_val v)) vals AbsVal.empty

  let resolve_loc l =
    if Loc.is_abstract_symloc l then (
      ( if not (Domain.LocTable.mem l !__absloc_map) then
        (* symbol $(s.access) is not resolved yet *)
        match Loc.to_symbol_opt l with Some s -> ignore (find s) | None -> () ) ;
      Domain.LocTable.find l !__absloc_map )
    else Loc.replace_loc_by_absval_map ~f:resolve_val l


  let resolve_use use =
    Disjunct.fold
      (fun s ->
        let _, symdiff = find s in
        Disjunct.union (SymDiff.uses_of symdiff) )
      use Disjunct.empty


  let is_symbol_changed s = SymDiff.is_diff (snd (find s))

  let resolve_pc ~astate_caller ~astate_callee =
    let open Domain in
    let pc_resolved =
      let single_f v =
        match AbsVal.is_singleton_or_more (resolve_val v) with
        | Empty ->
            Val.top_primitive
        | Singleton v' ->
            v'
        | More ->
            Val.top_primitive
      in
      PC.replace_by_map ~f:single_f astate_callee.pc |> PC.meet astate_caller.pc
    in
    if PC.is_invalid astate_caller.pc then (
      (* TODO: invalidate state with null.field loc or invalid type,
         but be cafeful about what should be invalidated: state or value *)
      L.d_printfln "@.===== Summary is invalidated by pathcond =====@." ;
      L.d_printfln " - caller state: %a@." Domain.pp astate_caller ;
      L.d_printfln " - callee state: %a@. - invalidated pc: %a@." Domain.pp astate_callee PC.pp
        astate_caller.pc ;
      None )
    else Some pc_resolved


  let resolve_state instr_node ~astate_caller astate : Domain.t option =
    let open Domain in
    (* compute differential memory from callee state *)
    let diff_mem =
      (* take callee's original state if they are changed *)
      match (astate.last_org, astate_caller.last_org) with
      | Original, Original ->
          astate.mem
      | (Current _ | Past _), Original | Original, (Current _ | Past _) ->
          (* original's uses are recored as Diff *)
          L.(die InternalError) "invalid last orgs"
      | (Current (_, original_state) | Past (_, original_state)), Past _ ->
          Mem.fold
            (fun l v acc -> if Mem.mem l acc then acc else Mem.add l v acc)
            original_state.mem astate.mem
      | (Current (_, original_state) | Past (_, original_state)), Current _ ->
          Mem.fold
            (fun l v acc ->
              let uses = Domain.LocUse.find l original_state.loc_use in
              if Mem.mem l acc then acc
              else if Disjunct.exists is_symbol_changed uses then Mem.add l v acc
              else acc )
            original_state.mem astate.mem
    in
    let memory =
      let _astate =
        Mem.fold
          (fun l v ->
            (* some l.f could be resolved to null.f, but does not mean the state is invalid *)
            let locs = resolve_loc l |> Loc.Set.filter (not <<< Loc.is_invalid) in
            let vals = resolve_vals v in
            Domain.store_locs instr_node locs (vals, SymDiff.diff) )
          diff_mem
          {astate_caller with mem= Mem.empty}
      in
      Domain.(_astate.mem)
    in
    try
      let vtmap =
        let update v ~caller_typ_opt ~callee_typ_opt vtmap =
          match callee_typ_opt with
          | Some callee_typ when is_strong_updatable_val astate v ->
              if AbsTyp.is_different caller_typ_opt callee_typ_opt then (
                L.d_printfln "type %a and %a are different, so invalidate this callee state (%a)"
                  (Pp.option AbsTyp.pp) caller_typ_opt (Pp.option AbsTyp.pp) callee_typ_opt Val.pp v ;
                raise (Unexpected "InconsistentType") )
              else VTMap.strong_update v callee_typ vtmap
          | Some callee_typ ->
              VTMap.weak_update v callee_typ vtmap
          | None ->
              vtmap
        in
        fold (* update default callee type because it could be non-default type for caller *)
          (fun s (resolved_val, _) acc ->
            match AbsVal.is_singleton_or_more resolved_val with
            | Singleton (VSymbol _ as v) ->
                let caller_typ_opt = try Some (read_typ astate_caller v) with _ -> None in
                let callee_typ_opt = try Some (read_typ astate (Val.VSymbol s)) with _ -> None in
                update v ~caller_typ_opt ~callee_typ_opt acc
            | _ ->
                acc )
          !__cache VTMap.empty
        |> VTMap.fold
             (fun v abstyp acc ->
               match v with
               | Val.VSymbol s when mem s !__cache ->
                   acc
               | _ -> (
                 match AbsVal.is_singleton_or_more (resolve_val v) with
                 | Singleton v ->
                     let caller_typ_opt = try Some (read_typ astate_caller v) with _ -> None in
                     let callee_typ_opt = Some abstyp in
                     update v ~caller_typ_opt ~callee_typ_opt acc
                 | _ ->
                     acc ) )
             astate.vtmap
      in
      let reg = Reg.empty in
      let pc = Option.value_exn (resolve_pc ~astate_caller ~astate_callee:astate) in
      let invalidated_values =
        AbsVal.fold (fun v -> AbsVal.union (resolve_val v)) astate.invalidated_values AbsVal.empty
      in
      let replaced_values =
        ReplacedValMap.fold
          (fun src dst acc ->
            let resolved_src = resolve_val src in
            let resolved_dst = resolve_val dst in
            match
              (AbsVal.is_singleton_or_more resolved_src, AbsVal.is_singleton_or_more resolved_dst)
            with
            | Singleton src', Singleton dst' ->
                ReplacedValMap.add src' dst' acc
            | _ ->
                acc )
          astate.replaced_values ReplacedValMap.empty
      in
      let assert_conds =
        AssertConds.map
          (fun (v1, v2, kind, node) ->
            let v1_resolved = resolve_vals v1 in
            let v2_resolved = resolve_vals v2 in
            (v1_resolved, v2_resolved, kind, node) )
          astate.assert_conds
      in
      let visited_allocs = astate.visited_allocs in
      let revisited_allocs = astate.revisited_allocs in
      let loc_use =
        LocUse.fold
          (fun l use ->
            let resolved_locs = resolve_loc l in
            let resolved_uses =
              try resolve_use use
              with e ->
                L.progress "there are unresolved symbols in loc_use: %a@." Domain.pp astate ;
                raise e
            in
            Loc.Set.fold (fun l' -> LocUse.update ~is_weak:true l' resolved_uses) resolved_locs )
          astate.loc_use LocUse.empty
      in
      let loc_def = LocDef.empty in
      let changed =
        let f s = find s in
        Changed.replace_if_unchanged astate.changed ~f
      in
      let last_org =
        match astate.last_org with
        | Past (callee_last_node, ostate) ->
            let org_mem =
              Mem.fold
                (fun l v acc ->
                  if Mem.mem l diff_mem then acc
                  else
                    let locs = resolve_loc l |> Loc.Set.filter (not <<< Loc.is_invalid) in
                    let vals = resolve_vals v in
                    Loc.Set.fold (fun l' -> Domain.Mem.weak_update l' vals) locs acc )
                ostate.mem Mem.empty
            in
            let org_loc_use =
              LocUse.fold
                (fun l use ->
                  let resolved_locs = resolve_loc l in
                  let resolved_uses = resolve_use use in
                  Loc.Set.fold
                    (fun l' -> LocUse.update ~is_weak:true l' resolved_uses)
                    resolved_locs )
                ostate.loc_use LocUse.empty
            in
            Past (callee_last_node, {ostate with mem= org_mem; loc_use= org_loc_use})
        | _ ->
            astate.last_org
      in
      Some
        { reg
        ; mem= memory
        ; pc
        ; vtmap
        ; visited_allocs
        ; revisited_allocs
        ; replaced_values
        ; invalidated_values
        ; assert_conds
        ; abs_patches= astate.abs_patches
        ; id_use= astate.id_use
        ; loc_use
        ; loc_def
        ; is_exceptional= astate.is_exceptional
        ; is_conditional= astate.is_conditional
        ; is_incomplete= astate.is_incomplete
        ; changed
        ; last_org
        ; current_proc= astate.current_proc
        ; current_ctxs= astate.current_ctxs
        ; control_deps= ControlDeps.bottom
        ; important_param= astate.important_param }
    with Unexpected "InconsistentType" -> None


  let update_caller_by_callee instr_node ~astate_caller ~astate_callee (ret_id, ret_typ) =
    let open Domain in
    if (not (Domain.is_exceptional astate_callee)) || Config.debug_level_analysis > 3 then
      L.d_printfln "Update by callee state@. - %a@." Domain.pp astate_callee ;
    let program = Program.from_marshal () in
    (* L.progress "Update caller by callee (%a, %a)@." Procname.pp astate_caller.current_proc InstrNode.pp instr_node ; *)
    let callee_pdesc = Program.pdesc_of program astate_callee.current_proc in
    let caller_pdesc = Program.pdesc_of program astate_caller.current_proc in
    let astate_caller, astate_callee =
      (* bind return variable to caller *)
      let ret_loc = Procdesc.get_ret_var callee_pdesc |> Loc.of_pvar in
      let astate_caller =
        if Domain.is_exceptional astate_callee then
          let caller_ret_loc = caller_pdesc |> Procdesc.get_ret_var |> Domain.Loc.of_pvar in
          let return_diffval = read_loc astate_callee (ret_loc, SymDiff.empty) in
          Domain.store_loc instr_node caller_ret_loc return_diffval astate_caller
        else if Typ.is_void ret_typ then astate_caller
        else
          let return_diffval =
            try read_loc astate_callee (ret_loc, SymDiff.empty)
            with e ->
              L.progress "no return for (%a, %a)@." Procname.pp astate_callee.current_proc
                (Typ.pp_full Pp.text) ret_typ ;
              raise e
          in
          Domain.store_reg ret_id return_diffval astate_caller
      in
      (* In case of recursive call, remove variables of callee before update *)
      let astate_callee = Domain.remove_locals ~pdesc:callee_pdesc astate_callee in
      (astate_caller, astate_callee)
    in
    let id_use = astate_caller.id_use in
    let current_ctxs =
      if Program.is_entry program astate_caller.current_proc then astate_caller.current_ctxs
      else if Domain.has_dummy_ctx astate_callee && Domain.has_past_original astate_caller then
        astate_caller.current_ctxs
      else Domain.Contexts.inter astate_caller.current_ctxs astate_callee.current_ctxs
    in
    let astate_caller, astate_callee =
      ( filter_by_invalid_values astate_caller ~invalid_values:astate_callee.invalidated_values
      , filter_by_invalid_values astate_callee ~invalid_values:astate_caller.invalidated_values )
    in
    let astate_caller =
      AssertConds.fold Domain.set_assertion astate_callee.assert_conds astate_caller
    in
    let astate_caller =
      (* update visited allocations before summary update *)
      let new_revisited_allocs =
        Node.Set.inter astate_callee.visited_allocs astate_caller.visited_allocs
        |> Node.Set.union astate_callee.revisited_allocs
      in
      { astate_caller with
        revisited_allocs= Node.Set.union new_revisited_allocs astate_caller.revisited_allocs }
    in
    let astate_caller =
      Mem.fold
        (fun l v ->
          let uses = LocUse.find l astate_callee.loc_use in
          let symdiff =
            if Domain.is_original astate_caller then SymDiff.of_uses uses else SymDiff.diff
          in
          store_loc instr_node l (v, symdiff) )
        astate_callee.mem astate_caller
      |> VTMap.fold (fun v abstyp -> store_typ (AbsVal.singleton v) abstyp) astate_callee.vtmap
    in
    let loc_use =
      if Domain.is_original astate_caller && Domain.is_original astate_callee then
        astate_caller.loc_use
      else (* loc_use could be updated at store_loc *) LocUse.empty
    in
    let loc_def =
      if Domain.is_original astate_caller && Domain.is_original astate_callee then
        astate_caller.loc_def
      else (* loc_def could be updated at store_loc *) LocDef.empty
    in
    let mem = astate_caller.mem in
    let vtmap = astate_caller.vtmap in
    let pc = PC.meet astate_caller.pc astate_callee.pc in
    let invalidated_values = astate_caller.invalidated_values in
    let replaced_values = astate_caller.replaced_values in
    let visited_allocs = Node.Set.union astate_caller.visited_allocs astate_callee.visited_allocs in
    let revisited_allocs =
      Node.Set.union astate_caller.revisited_allocs astate_callee.revisited_allocs
    in
    let assert_conds = astate_caller.assert_conds in
    let abs_patches =
      match (astate_caller.abs_patches, astate_callee.abs_patches) with
      | None, None ->
          None
      | Some abs_patches, None | None, Some abs_patches ->
          Some abs_patches
      | Some abs_patches_caller, Some abs_patches_callee ->
          Some (Fault.Set.inter abs_patches_caller abs_patches_callee)
    in
    (* let changed = Changed.fold Changed.add_disjunct astate_callee.changed astate_caller.changed in *)
    let changed = Changed.update_by_callee astate_callee.changed astate_caller.changed in
    let last_org =
      (* if org_flow is false, last_org must have some original state *)
      match (astate_caller.last_org, astate_callee.last_org) with
      | Current _, Current _ ->
          astate_caller.last_org
      | Current (_, ostate_caller), Past (_, ostate_callee) ->
          let ostate_caller =
            Mem.fold
              (fun l v ->
                let uses = LocUse.find l ostate_callee.loc_use in
                store_loc instr_node l (v, SymDiff.of_uses uses) )
              ostate_callee.mem ostate_caller
          in
          Past (instr_node, ostate_caller)
      | Past _, _ ->
          (* all callees states are updated by diff *)
          astate_caller.last_org
      | Original, Original ->
          Original
      | _ ->
          L.(die InternalError)
            "invalid last original@.-----caller------@.%a@.------callee------@.%a@." pp
            astate_caller pp astate_callee
    in
    let is_incomplete = astate_caller.is_incomplete || astate_callee.is_incomplete in
    let astate_caller =
      Domain.
        { reg= astate_caller.reg
        ; mem
        ; pc
        ; vtmap
        ; visited_allocs
        ; revisited_allocs
        ; replaced_values
        ; invalidated_values
        ; assert_conds
        ; abs_patches
        ; id_use
        ; loc_use
        ; loc_def
        ; is_exceptional=
            astate_callee.is_exceptional (* since exceptional state cannot execute fuction *)
        ; is_conditional= false (* actually, false *)
        ; is_incomplete
        ; changed
        ; last_org
        ; current_proc= astate_caller.current_proc
        ; current_ctxs
        ; control_deps= astate_caller.control_deps
        ; important_param= astate_caller.important_param }
    in
    if Domain.PC.is_invalid astate_caller.pc then (
      (* TODO: invalidate state with null.field loc or invalid type,
         but be cafeful about what should be invalidated: state or value *)
      L.d_printfln "@.===== Summary is invalidated by pathcond =====@." ;
      L.d_printfln " - caller state: %a@." Domain.pp astate_caller ;
      L.d_printfln " - callee state: %a@. - invalidated pc: %a@." Domain.pp astate_callee PC.pp
        astate_caller.pc ;
      None )
    else (
      if (not (Domain.is_exceptional astate_callee)) || Config.debug_level_analysis > 3 then
        L.d_printfln "Updated state@. - %a@." Domain.pp astate_caller ;
      Some astate_caller )
end

(* Check if the patch sets are consistent.
   * Basically, it checks if the caller's and callee's patches have common patchs.
*)
let is_patch_consistent_check astate callee_summary =
  let open Domain in
  match (astate.abs_patches, callee_summary.abs_patches) with
  | None, None ->
      true
  | None, Some _ ->
      Domain.is_original astate
  | Some _, None ->
      true
  | Some caller_abs_patches, Some callee_abs_patches ->
      not (Fault.Set.disjoint caller_abs_patches callee_abs_patches)


(* Check if the test context is consistent.
   * Basically, it checks if a common context exists between the caller's and the callee's.
   * For the dummy context, which means "any" context, it could be always consistent
*)
let is_context_consistent_check program node astate callee_summary =
  let open Domain in
  let caller_ctxs =
    if Program.is_entry program astate.current_proc then
      (* If the caller is test entry, make the current node as context *)
      let testClass =
        match Contexts.choose astate.current_ctxs with
        | Empty testClass ->
            testClass
        | _ ->
            L.(die InternalError) "invalid entry contexts"
      in
      Contexts.add (Test (testClass, node)) astate.current_ctxs
    else astate.current_ctxs
  in
  match (caller_ctxs, callee_summary.current_ctxs) with
  | _ when Domain.has_dummy_ctx callee_summary ->
      (* No need to analyze callee if caller is original, and THERE EXIST original callee states *)
      Domain.has_dummy_ctx astate || Domain.has_past_original astate || Config.sprint_no_test
  | _ when Procname.is_java_class_initializer callee_summary.current_proc ->
      (* Class initializer can only be called from the entry *)
      Program.is_entry program astate.current_proc
  | _ when Program.is_entry program astate.current_proc && Domain.has_past_original astate -> (
    (* Dummy context summary may be not prepared for MODIFIED method 
     * In this case, just check test classes are equal *)
    match (Contexts.choose caller_ctxs, Contexts.choose callee_summary.current_ctxs) with
    | Test (testClass, _), Test (calleeTestClass, _) ->
        Typ.Name.equal testClass calleeTestClass
    | _ ->
        false )
  | lhs, rhs ->
      not (Contexts.disjoint lhs rhs)


(* Check if the type of the callee is consistent with the caller's type
   * Note: This check can be costly in terms of performance:
     including matching the types of symbols in the callee with the caller's.
*)
let is_consistent_type_check astate actual_values formals callee_summary =
  let open Domain in
  let check_abstyp ~callee_vals ~caller_vals ~caller_abstyp ~callee_abstyp =
    if AbsTyp.is_different (Some caller_abstyp) (Some callee_abstyp) then (
      L.d_printfln "type %a and %a are different, so invalidate this callee state (%a vs %a)"
        AbsTyp.pp caller_abstyp AbsTyp.pp callee_abstyp AbsVal.pp caller_vals AbsVal.pp callee_vals ;
      false )
    else true
  in
  let is_callee_consistent, _ =
    AbsVal.fold
      (fun v (acc, astate) ->
        match v with
        | _ when not acc ->
            (acc, astate)
        | Val.VSymbol s ->
            let callee_abstyp = read_typ callee_summary (Val.VSymbol s) in
            let caller_vals, _ = SymResolvedMap.find s in
            let callee_vals = AbsVal.singleton (Val.VSymbol s) in
            let caller_abstyp = read_typ_of_vals astate caller_vals in
            let astate = store_typ caller_vals callee_abstyp astate in
            (acc && check_abstyp ~callee_vals ~caller_vals ~callee_abstyp ~caller_abstyp, astate)
        | _ ->
            (acc, astate) )
      callee_summary.important_param (true, astate)
  in
  is_callee_consistent
  && List.mapi actual_values ~f:(fun i v -> (i, v))
     |> List.fold2_exn formals ~init:true ~f:(fun acc (fv, _) (i, (caller_vals, _)) ->
            if not acc then acc
            else
              let caller_abstyp = read_typ_of_vals astate caller_vals in
              let callee_vals = AbsVal.singleton (Val.VSymbol (Symbol.of_pvar i fv)) in
              let callee_abstyp = read_typ_of_vals callee_summary callee_vals in
              acc && check_abstyp ~callee_vals ~caller_vals ~callee_abstyp ~caller_abstyp )


(* Check if dynamic info, whether the method call executed well or not, is consistent
   * If the caller diverged from the original execution, then it is always consistent
   * Otherwise, should follow the dynamic info (i.e., is_exceptional = !dynamic_info.well_executed)
   * , either the callee execution diverged from the original execution (i.e., Past)
*)
let is_consistent_die_check node astate callee_summary =
  let open Domain in
  match (find_dynamic_exprs astate node, Node.get_instr node) with
  | _, Sil.Call (_, Const (Cfun (Java mthd)), _, _, _)
    when Fl4aprModels.Assert.implements (Procname.Java.get_class_type_name mthd) ->
      (* FIXME: WHAT IS THIS ??? *)
      true
  | _, _ when has_past_original astate || has_past_original callee_summary ->
      true
  | V false, _ ->
      is_exceptional callee_summary
  | V true, _ ->
      not (is_exceptional callee_summary)
  | _ ->
      true


(* Check if path condition is satisfiable *)
let is_consistent_pc_check astate callee_summary =
  match SymResolvedMap.resolve_pc ~astate_caller:astate ~astate_callee:callee_summary with
  | Some _ ->
      true
  | None ->
      false


(* Check if caller satisfied the callee's changed condition 
 * e.g., if callee assume that parameter 'x' is different from the original execution's 
         then, caller must have changed 'x' *)
let is_consistent_change_check astate callee_summary =
  let open Domain in
  let is_symbol_changed = SymResolvedMap.is_symbol_changed in
  if not (is_original astate) then Changed.is_changed ~is_symbol_changed callee_summary.changed
  else
    let f s = SymResolvedMap.find s in
    Changed.is_changable ~f callee_summary.changed


(* Check execution flow consistency: 
 * Original flow can follow to the original flow, or diverged from the original 
   * e.g., Original -> Current -> Past is ok
 * However, diverged flow (Past) cannot follow to the original flow
   * e.g., Past -> Original/Current contradicts the flow 
   * Simliary, Past -> Past/Current is not allowed 
     since callee's Past/Current assume that entry point is Original 
 * Exception: the case for re-entering a modified buggy method after passing the failing statement 
   * e.g., c1: buggy_method_modified(x); c2: buggy_method_modified(y);
   * For modified method, summary with dummy context is not prepared.
   * So we allow the Past -> Past flow only for this case
 *)
let is_consistent_flow_check _ astate callee_summary =
  let open Domain in
  match (astate.last_org, callee_summary.last_org) with
  | Original, _ ->
      true
  | Current _, _ ->
      true
  | Past _, Past _ when Program.is_entry (Program.from_marshal ()) astate.current_proc ->
      (* For case re-entering MODIFIED buggy method after passing the failing statement *)
      true
  | Past _, _ ->
      Domain.has_dummy_ctx callee_summary


let is_consistent_summary program node ~astate ~actual_values ~formals callee_summary =
  let with_print check_func msg =
    if check_func () then true
    else (
      L.d_printfln "%s failed! %a" msg Domain.pp_sig callee_summary ;
      false )
  in
  with_print (fun () -> is_patch_consistent_check astate callee_summary) "fault consistency"
  && with_print
       (fun () -> is_context_consistent_check program node astate callee_summary)
       "context consistency"
  && with_print
       (fun () -> is_consistent_type_check astate actual_values formals callee_summary)
       "type consisteny"
  && with_print (fun () -> is_consistent_die_check node astate callee_summary) "die consistency"
  && with_print (fun () -> is_consistent_pc_check astate callee_summary) "pc consistency"
  && with_print (fun () -> is_consistent_change_check astate callee_summary) "change consistency"
  && with_print
       (fun () -> is_consistent_flow_check program astate callee_summary)
       "flow consistency"


let resolve_summary node ~astate_caller ~callee_summary ret_id : Domain.t option =
  let open Domain in
  if (not (is_exceptional callee_summary)) || Config.debug_level_analysis > 3 then
    L.d_printfln "[DEBUG]: resolving info for %a" Procname.pp Domain.(callee_summary.current_proc) ;
  L.d_printfln "[Caller Sig]: %a" Domain.pp_sig astate_caller ;
  (* L.d_printfln "[DEBUG]: sym_resolved_map@. - %a@.====================================@." SymResolvedMap.pp
     !SymResolvedMap.__cache ; *)
  match SymResolvedMap.resolve_state ~astate_caller node callee_summary with
  | Some callee_summary_resolved ->
      if (not (Domain.is_exceptional callee_summary)) || Config.debug_level_analysis > 3 then
        L.d_printfln "Callee state before resolving@. - %a@." Domain.pp callee_summary ;
      SymResolvedMap.update_caller_by_callee node ~astate_caller
        ~astate_callee:callee_summary_resolved ret_id
  | None ->
      None


let resolve_summaries program astate node ~(actual_values : DiffVal.t list) ~formals
    callee_summaries (ret_id, ret_typ) : Domain.t list =
  let open Domain in
  let callee_disjuncts = get_disjuncts callee_summaries in
  let num_callee = List.length callee_disjuncts in
  let callee_disjuncts =
    List.filter callee_disjuncts
      ~f:(is_consistent_summary program node ~astate ~actual_values ~formals)
  in
  let callee_original_states, callee_diff_states =
    List.partition_tf callee_disjuncts ~f:Domain.is_original
  in
  let is_caller_org = Domain.is_original astate in
  L.d_printfln " - find %d original summaries"
    (List.length (List.filter callee_disjuncts ~f:Domain.is_original)) ;
  L.d_printfln "consistent summaries before resolution: got %d from %d"
    (List.length callee_disjuncts) num_callee ;
  let original_post_callee_ctxs_list =
    if is_caller_org then
      List.filter_map callee_original_states ~f:(fun callee_summary ->
          match resolve_summary node ~astate_caller:astate ~callee_summary (ret_id, ret_typ) with
          | Some opost ->
              Some (opost, Domain.(callee_summary.current_ctxs))
          | None ->
              None )
    else []
  in
  let diff_posts =
    (* computing diff * diff *)
    let callee_diff_states =
      Domain.match_diff_original callee_diff_states callee_original_states
      |> List.map ~f:(fun (org_state_opt, callee_summary) ->
             match (org_state_opt, callee_summary.last_org) with
             | None, Current (node', ostate) ->
                 Domain.set_past node' ~ostate callee_summary
             | _ ->
                 callee_summary )
    in
    if is_caller_org then
      (* computing org * diff *)
      let astate_caller = Domain.set_diff node astate in
      List.filter_map callee_diff_states ~f:(fun callee_summary ->
          resolve_summary node ~astate_caller ~callee_summary (ret_id, ret_typ) )
    else
      (* computing diff * diff
         computing diff * org *)
      let astate_caller = astate in
      List.map callee_original_states ~f:(Domain.set_diff node) @ callee_diff_states
      |> List.filter_map ~f:(fun callee_summary ->
             resolve_summary node ~astate_caller ~callee_summary (ret_id, ret_typ) )
  in
  List.map ~f:fst original_post_callee_ctxs_list @ diff_posts


let instantiate_summary program astate interproc node instr (ret_id, ret_typ) arg_typs callee =
  match Program.pdesc_of_opt program callee with
  | Some callee_pdesc -> (
      let callee = Procdesc.get_proc_name callee_pdesc in
      let instr_node = InstrNode.of_pnode node instr in
      let formals = Procdesc.get_pvar_formals callee_pdesc in
      let actual_values =
        try List.mapi arg_typs ~f:(fun _ (arg, _) -> Domain.eval astate node instr arg)
        with exn ->
          L.progress "FAILED to instantiate summary: exception while evaluating actual values@.%a@."
            Domain.pp astate ;
          raise exn
      in
      match interproc callee with
      | Some callee_summary ->
          SymResolvedMap.init astate instr_node ~formals ~actual_values ;
          let resolved_disjuncts =
            resolve_summaries program astate instr_node ~actual_values ~formals callee_summary
              (ret_id, ret_typ)
          in
          L.d_printfln "%d states are instantiated from %d summaries from %a"
            (List.length resolved_disjuncts)
            (get_disjuncts callee_summary |> List.length)
            Procname.pp callee ;
          Some resolved_disjuncts
      | None ->
          None )
  | None ->
      None


let init proc_desc : Domain.t list =
  let program = Program.from_marshal () in
  let formals = Procdesc.get_pvar_formals proc_desc in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let entry_node = Procdesc.get_start_node proc_desc in
  let instr_node = InstrNode.of_pnode entry_node Sil.skip_instr in
  let init = Domain.set_current_proc Domain.bottom proc_name in
  let astate =
    List.foldi formals ~init ~f:(fun i astate (pv, _) ->
        let symbol = Symbol.of_pvar i pv in
        let value = AbsVal.singleton (Val.VSymbol symbol) in
        let symdiff = SymDiff.of_uses (Disjunct.singleton symbol) in
        let diffval = if Config.sprint_exnchecker then DiffVal.top else (value, symdiff) in
        Domain.store_loc instr_node (Loc.of_pvar pv) diffval astate )
  in
  (* HEURISTICS: important parameters to prevent states being merged *)
  let important_param =
    List.concat_mapi formals ~f:(fun i (pv, typ) ->
        if String.is_suffix ~suffix:"cb" (Pvar.to_string pv) then [Val.VSymbol (Symbol.of_pvar i pv)]
        else
          match Typ.name (strip_ptr typ) with
          | Some name -> (
            match Program.Class.lookup program name with
            | Some Struct.{fields} ->
                List.filter_map fields ~f:(fun (fn, _, _) ->
                    if String.is_suffix (Fieldname.to_simplified_string fn) ~suffix:"callback" then
                      Some (Val.VSymbol (Symbol.append_field (Symbol.of_pvar i pv) ~fn))
                    else if String.is_suffix (Fieldname.to_simplified_string fn) ~suffix:"Callback"
                    then Some (Val.VSymbol (Symbol.append_field (Symbol.of_pvar i pv) ~fn))
                    else None )
            | None ->
                [] )
          | None ->
              [] )
    |> AbsVal.of_list
  in
  let astate = Domain.{astate with important_param} in
  List.map (DynInfo.ctxs_of_proc proc_name) ~f:(Domain.set_ctx astate)
