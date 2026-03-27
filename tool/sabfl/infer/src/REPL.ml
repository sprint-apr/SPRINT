(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

(** Top-level driver that orchestrates build system integration, frontends, backend, and reporting *)

module CLOpt = CommandLineOption
module L = Logging

let run driver_mode =
  let open Driver in
  run_prologue driver_mode ;
  let changed_files = read_config_changed_files () in
  InferAnalyze.invalidate_changed_procedures changed_files ;
  capture driver_mode ~changed_files ;
  analyze_and_report driver_mode ~changed_files ;
  run_epilogue ()


let run driver_mode = ScubaLogging.execute_with_time_logging "run" (fun () -> run driver_mode)

let setup () =
  let db_start =
    let already_started = ref false in
    fun () ->
      if (not !already_started) && CLOpt.is_originator && DBWriter.use_daemon then (
        DBWriter.start () ;
        Epilogues.register ~f:DBWriter.stop ~description:"Stop Sqlite write daemon" ;
        already_started := true )
  in
  if not Config.sprint_resolve_recursive then
    Vocab.create_dir ~remove:true Config.sprint_summary_dir ;
  Vocab.create_dir ~remove:true Config.sprint_result_dir ;
  Vocab.create_dir ~remove:true (Config.sprint_result_dir ^ "_weak") ;
  ResultsDir.assert_results_dir "please run an infer analysis or capture first" ;
  let has_result_dir = true in
  if has_result_dir then (
    db_start () ;
    if CLOpt.is_originator then ResultsDir.RunState.add_run_to_sequence () ) ;
  has_result_dir


let print_active_checkers () =
  (if Config.print_active_checkers && CLOpt.is_originator then L.result else L.environment_info)
    "Active checkers: %a@."
    (Pp.seq ~sep:", " RegisterCheckers.pp_checker)
    (RegisterCheckers.get_active_checkers ())


let print_scheduler () =
  L.environment_info "Scheduler: %s@\n"
    ( match Config.scheduler with
    | File ->
        "file"
    | Restart ->
        "restart"
    | SyntacticCallGraph ->
        "callgraph" )


let print_cores_used () = L.environment_info "Cores used: %d@\n" Config.jobs

let log_environment_info () =
  L.environment_info "CWD = %s@\n" (Sys.getcwd ()) ;
  ( match Config.inferconfig_file with
  | Some file ->
      L.environment_info "Read configuration in %s@\n" file
  | None ->
      L.environment_info "No .inferconfig file found@\n" ) ;
  L.environment_info "Project root = %s@\n" Config.project_root ;
  let infer_args =
    Sys.getenv CLOpt.args_env_var
    |> Option.map ~f:(String.split ~on:CLOpt.env_var_sep)
    |> Option.value ~default:["<not set>"]
  in
  L.environment_info "INFER_ARGS = %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    infer_args ;
  L.environment_info "command line arguments: %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    (Array.to_list Sys.(get_argv ())) ;
  ( match Utils.get_available_memory_MB () with
  | None ->
      L.environment_info "Could not retrieve available memory (possibly not on Linux)@\n"
  | Some available_memory ->
      L.environment_info "Available memory at startup: %d MB@\n" available_memory ;
      ScubaLogging.log_count ~label:"startup_mem_avail_MB" ~value:available_memory ) ;
  print_active_checkers () ;
  print_scheduler () ;
  print_cores_used ()


let initialize () =
  ignore (setup ()) ;
  let program = Program.from_marshal ~init:true () in
  let faulty_locs = SBFL.parse_bug_positions program in
  let abs_patches =
    List.fold faulty_locs ~init:[] ~f:(fun acc loc -> Data.Fault.enumerate loc @ acc)
  in
  L.progress "Faults enumerated!:@." ;
  List.iter ~f:(fun fault -> L.progress "%a@." Data.Fault.pp_full fault) abs_patches ;
  Data.Fault.to_marshal abs_patches ;
  List.iter abs_patches ~f:(fun fault -> ignore (ISynthesizer.PatchTemplate.generate_patches fault))


let enum_abs_patches () =
  let faulty_locs = SBFL.parse_bug_positions (Program.from_marshal ()) in
  let abs_patches =
    List.fold faulty_locs ~init:[] ~f:(fun acc loc -> Data.Fault.enumerate loc @ acc)
  in
  L.progress "Faults enumerated!:@." ;
  List.iter ~f:(fun fault -> L.progress "%a@." Data.Fault.pp_full fault) abs_patches ;
  abs_patches


let example_fault =
  initialize () ;
  enum_abs_patches ()
