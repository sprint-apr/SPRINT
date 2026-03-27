open! Vocab
module F = Format
module L = Logging
module CFG = ProcCfg.Exceptional
module Node = InstrNode
module BottomUpAnalysis = SpecCheckerSummary
module Models = BasicDom.Models
module Domain = SpecCheckerDomain
module Fault = Domain.Fault
module Contexts = Domain.Contexts

module DisjunctiveConfig : TransferFunctions.DisjunctiveConfig = struct
  let join_policy = `UnderApproximateAfter 20

  let widen_policy = `UnderApproximateAfterNumIterations 2
end

module DisjReady = SpecCheckerCore.Make (SpecCheckerSummary)
module Analyzer = Fl4aprSymExecutor.Make (DisjReady) (DisjunctiveConfig)

let summary_serializer : SpecCheckerSummary.t Serialization.serializer =
  Serialization.create_serializer Serialization.Key.summary


let read_summary proc =
  Filename.concat Config.sprint_summary_dir (Procname.to_filename proc ^ ".specs")
  |> DB.filename_from_string
  |> Serialization.read_from_file summary_serializer


let store_inv_map proc (inv_map : Analyzer.invariant_map) =
  let path = Filename.concat Config.sprint_summary_dir (Procname.to_filename proc ^ ".invmap") in
  Utils.with_file_out path ~f:(fun oc -> Marshal.to_channel oc inv_map [])


let _proc_to_inv_map = ref Procname.Map.empty

let read_inv_map proc : Analyzer.invariant_map =
  match Procname.Map.find_opt proc !_proc_to_inv_map with
  | Some inv_map ->
      inv_map
  | None -> (
      let path =
        Filename.concat Config.sprint_summary_dir (Procname.to_filename proc ^ ".invmap")
      in
      try
        match Sys.is_file path with
        | `Yes ->
            let inv_map = Utils.with_file_in path ~f:Marshal.from_channel in
            _proc_to_inv_map := Procname.Map.add proc inv_map !_proc_to_inv_map ;
            inv_map
        | _ ->
            L.(die InternalError "Invmap does not exist %s") path
      with _ -> L.(die InternalError "Failed to read invmap %s") path )


let compute_invariant_map ~initial analysis_data proc_desc : Analyzer.invariant_map =
  Analyzer.exec_pdesc ~do_narrowing:false ~initial analysis_data proc_desc


let cached_compute_invariant_map ~initial analysis_data proc_desc =
  compute_invariant_map ~initial analysis_data proc_desc


let compute_summary : Procdesc.t -> CFG.t -> Analyzer.invariant_map -> SpecCheckerSummary.t =
 fun proc_desc cfg inv_map ->
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some exit_state ->
      SpecCheckerSummary.to_summary proc_desc exit_state
  | None ->
      SpecCheckerSummary.empty


let merge_invariant_map : Analyzer.invariant_map -> Analyzer.invariant_map -> Analyzer.invariant_map
    =
  CFG.Node.IdMap.merge (fun _ lhs_state_opt rhs_state_opt ->
      match (lhs_state_opt, rhs_state_opt) with
      | Some lhs_state, Some rhs_state ->
          Some
            Fl4aprSymExecutor.State.
              { pre= lhs_state.pre @ rhs_state.pre
              ; post= lhs_state.post @ rhs_state.post
              ; visit_count= lhs_state.visit_count }
      | Some lhs_state, None ->
          Some lhs_state
      | None, Some rhs_state ->
          Some rhs_state
      | None, None ->
          None )


let checker {InterproceduralAnalysis.analyze_dependency; proc_desc} =
  let interproc callee =
    match analyze_dependency callee with Some (_, summary) -> Some summary | None -> None
  in
  let procname = Procdesc.get_proc_name proc_desc in
  let analysis_data = DisjReady.analysis_data interproc procname in
  if Program.is_sliced_method analysis_data.program procname then None
  else if Config.sprint_preanal then None
  else
    let program = analysis_data.program in
    let cfg = CFG.from_pdesc proc_desc in
    let initial = SpecCheckerSummary.init proc_desc in
    let initial =
      if Program.is_entry program procname then
        List.concat_map initial ~f:(fun astate ->
            let testClass =
              match Contexts.choose Domain.(astate.current_ctxs) with
              | Empty testClass ->
                  testClass
              | _ ->
                  L.(die InternalError) "initial entry state should have testClass context"
            in
            let clinits =
              let abs_patches =
                if Config.sprint_exnchecker then Fault.from_marshal ()
                else Fault.from_marshal ~path:"abs_patches_to_analyze.data" ()
              in
              Program.all_procs program
              |> Procname.Set.filter (function
                   | Java mthd ->
                       Procname.Java.is_class_initializer mthd
                   | _ ->
                       false )
              |> Procname.Set.filter (not <<< Program.is_sliced_method program)
              |> Procname.Set.filter (fun proc ->
                     List.exists abs_patches ~f:(Procname.equal proc <<< Fault.get_proc_name) )
              |> Procname.Set.filter (fun proc ->
                     not (Domain.Contexts.is_empty (DynInfo.ctxs_of_proc_visited proc)) )
            in
            let junit_node =
              Program.node_for_junit_premethods program ~pdesc_opt:(Some proc_desc) ~clinits
                testClass procname
            in
            AnalysisCallbacks.html_debug_new_node_session
              (Procdesc.get_start_node proc_desc)
              ~kind:`ComputePre
              ~pp_name:(fun fmt -> F.fprintf fmt "==== Executing JUnit Instrs ====@.")
              ~f:(fun () ->
                Analyzer.exec_node_instrs None ~pp_instr:Fl4aprSymExecutor.pp_sil_instr
                  analysis_data junit_node [astate] ) )
      else initial
    in
    let inv_map = cached_compute_invariant_map ~initial analysis_data proc_desc in
    let rec reanalyze_by_summary prev_summary =
      let interproc proc =
        if Procname.equal proc procname then (
          L.d_printfln " - get summary from pre-analyzed summary -" ;
          Some prev_summary )
        else interproc proc
      in
      let analysis_data = DisjReady.analysis_data interproc procname in
      let inv_map = cached_compute_invariant_map ~initial analysis_data proc_desc in
      (inv_map, compute_summary proc_desc cfg inv_map)
    in
    let _, summary =
      let first_summary = compute_summary proc_desc cfg inv_map in
      if (not Config.sprint_resolve_recursive) && Program.is_self_recursive procname then (
        L.debug L.Analysis L.Quiet "[PROGRESS]: recursively analyze %a@." Procname.pp procname ;
        reanalyze_by_summary first_summary )
      else (inv_map, first_summary)
    in
    Some summary
