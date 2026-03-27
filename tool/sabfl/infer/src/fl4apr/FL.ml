open! IStd
open! Vocab
module L = Logging
module F = Format
module Procs = AbstractDomain.FiniteSet (Procname)
module FaultMap = WeakMap.Make (Fault) (Procs)
module Result = BasicDom.Result
module Domain = SpecCheckerDomain
module Summary = SpecCheckerSummary

let is_valid_exn ~expected_exn test_method astate =
  let ret_loc =
    Program.pdesc_of (Program.from_marshal ()) test_method
    |> Procdesc.get_ret_var |> Domain.Loc.of_pvar
  in
  match expected_exn with
  | Some typ -> (
    match Domain.read_loc_opt astate ret_loc with
    | Some ret_val ->
        L.progress "check whether %a is valid exception %a" Domain.AbsVal.pp ret_val
          (Typ.pp_full Pp.text) typ ;
        let exn_typ = Domain.read_typ_of_vals astate ret_val in
        Domain.is_satisfiable astate && Domain.is_exceptional astate
        && Domain.AbsTyp.is_different (Some exn_typ) (Some (Domain.AbsTyp.make_instance typ)) |> not
    | None ->
        false )
  | None ->
      (not (Domain.is_exceptional astate)) && Domain.is_satisfiable astate


let get_expected_exn_typ test_method =
  let program = Program.from_marshal () in
  let pdesc = Program.pdesc_of program test_method in
  let proc_attrs = Procdesc.get_attributes pdesc in
  let method_annot = ProcAttributes.(proc_attrs.method_annotation) in
  let open Annot in
  let res =
    List.find_map
      Method.(method_annot.return :: method_annot.params)
      ~f:(fun item ->
        List.find_map item ~f:(fun (annot, _) ->
            match find_parameter annot ~name:"expected" with
            | Some (Class typ) ->
                Some typ
            | _ ->
                None ) )
  in
  ( match res with
  | Some typ ->
      L.progress "Expected exn typ: %a@." (Typ.pp_full Pp.text) typ
  | None ->
      () ) ;
  res


let get_summary_from_test_method get_summary (klass, test_proc) =
  Option.value_map (get_summary test_proc) ~default:[] ~f:(fun summary ->
      Summary.get_local_disjuncts summary )
  (* filter by actual test class *)
  |> List.filter ~f:(fun astate ->
         Domain.Contexts.exists
           (function
             | Domain.Context.Empty test_class | Domain.Context.Test (test_class, _) ->
                 Typ.Name.equal test_class klass
             | _ ->
                 false )
           astate.Domain.current_ctxs )


let validate_fault_by_single_tc get_summary fault (klass, test_proc) : Fault.result =
  let expected_exn_typ = get_expected_exn_typ test_proc in
  let fault_states =
    List.filter
      (get_summary_from_test_method get_summary (klass, test_proc))
      ~f:(fun astate ->
        match Domain.(astate.abs_patches) with
        | Some abs_patches ->
            Option.is_some (Fault.Set.find_opt fault abs_patches)
        | None ->
            false )
  in
  let is_satisfiable astate = is_valid_exn ~expected_exn:expected_exn_typ test_proc astate in
  let sat_states, unsat_states = List.partition_tf fault_states ~f:is_satisfiable in
  let is_sat = not (List.is_empty sat_states) in
  if Config.sprint_exnchecker then
    if is_sat then Fault.ExnSAT
    else if List.is_empty fault_states then
      let faulty_proc = Fault.get_proc_name fault in
      let ctxs = DynInfo.ctxs_of_proc_visited faulty_proc in
      if
        Domain.Contexts.exists
          (function
            | Domain.Context.Test (test_class, node) ->
                Procname.equal test_proc (InstrNode.get_proc_name node)
                && Typ.Name.equal test_class klass
            | _ ->
                false )
          ctxs
      then Fault.Unsound
      else Fault.Unexecuted
    else Fault.ExnUnSAT
  else
    let is_assert_checked =
      match expected_exn_typ with
      | _ when List.is_empty sat_states && List.is_empty unsat_states ->
          false
      | Some _ ->
          true
      | None ->
          (* test is executed, but patch does not affect it at all *)
          List.exists unsat_states ~f:(not <<< Domain.is_exceptional)
    in
    if is_sat then Fault.SAT else if is_assert_checked then Fault.UnSAT else Fault.NoChange


let validate_fault_by_single_tc get_summary fault (klass, test_proc) : Fault.result =
  match Utils.read_file Config.sprint_preanalysis_result with
  | Ok ["Unreachable"] ->
      (* Use only fault method's summary to check if the faulty state has been changed by the patch *)
      let fault_states =
        List.filter
          (get_summary_from_test_method get_summary (klass, Fault.get_proc_name fault))
          ~f:(fun astate ->
            match Domain.(astate.abs_patches) with
            | Some abs_patches ->
                Option.is_some (Fault.Set.find_opt fault abs_patches)
            | None ->
                false )
      in
      let is_sat = List.exists fault_states ~f:Domain.has_past_original in
      if Config.sprint_exnchecker then Fault.ExnSAT
      else if is_sat then Fault.SAT
      else Fault.NoChange
  | Ok [("Analysis" | "Default")] ->
      validate_fault_by_single_tc get_summary fault (klass, test_proc)
  | _ ->
      L.die InternalError "Failed to read preanalysis result"


let validate_aps_by_nontrivial_summaries get_summary program test_methods abs_patches =
  let open Domain in
  let module ContextMap = PrettyPrintable.MakePPMap (Context) in
  let test_methods = List.mapi test_methods ~f:(fun i test_method -> (i, test_method)) in
  let ctx_to_test_id_map =
    Contexts.fold
      (fun ctx ->
        let test_ids =
          match ctx with
          | Empty testClass ->
              List.filter test_methods ~f:(fun (_, (klass, _)) -> Typ.Name.equal testClass klass)
              |> List.map ~f:fst
          | Test (testClass, node) ->
              List.filter test_methods ~f:(fun (_, (klass, proc)) ->
                  Typ.Name.equal testClass klass
                  && Procname.equal proc (InstrNode.get_proc_name node) )
              |> List.map ~f:fst
          | _ ->
              []
        in
        ContextMap.add ctx test_ids )
      (DynInfo.all_ctxs ()) ContextMap.empty
  in
  let ctxs_to_test_ids ctxs =
    Contexts.fold
      (fun ctx acc ->
        match ContextMap.find_opt ctx ctx_to_test_id_map with
        | Some test_ids ->
            Int.Set.union acc (Int.Set.of_list test_ids)
        | None ->
            acc )
      ctxs Int.Set.empty
  in
  (* construct PatchId -> 2^{TestId} *)
  (* 1. no normal & original state in summary
     2. normal & patched state exist in summary
     3. at non-test procedures *)
  let ap_to_feasible_tests =
    List.filter_map
      (Program.all_procs program |> Procname.Set.elements)
      ~f:(fun proc ->
        get_summary proc
        |> Option.map ~f:(fun summary -> (proc, Summary.get_local_disjuncts summary)) )
    (* get only test failing procs *)
    |> List.filter ~f:(fun (_, disjuncts) ->
           List.for_all disjuncts ~f:(fun astate ->
               (not (is_original astate)) || is_exceptional astate ) )
    |> List.fold ~init:Int.Map.empty ~f:(fun acc (proc, disjuncts) ->
           let _debug_abs_patches = ref Fault.Set.empty in
           let patches_and_test_ids =
             List.filter_map disjuncts ~f:(fun astate ->
                 match (astate.abs_patches, astate.last_org) with
                 | Some abs_patches, Past _
                   when (not (is_exceptional astate))
                        && not (Program.is_entry program astate.current_proc) ->
                     _debug_abs_patches := Fault.Set.union abs_patches !_debug_abs_patches ;
                     Some (abs_patches, ctxs_to_test_ids astate.current_ctxs)
                 | _ ->
                     None )
           in
           if not (Fault.Set.is_empty !_debug_abs_patches) then
             L.debug L.Analysis L.Quiet "======= Feasible AbsPatches in %a ==========@.%a@."
               Procname.pp proc Fault.Set.pp !_debug_abs_patches ;
           List.fold patches_and_test_ids ~init:acc ~f:(fun acc (abs_patches, tests) ->
               Fault.Set.fold
                 (fun abs_patch acc ->
                   Int.Map.update acc
                     Fault.(abs_patch.id)
                     ~f:(fun tests' ->
                       Int.Set.union tests (Option.value ~default:Int.Set.empty tests') ) )
                 abs_patches acc ) )
  in
  List.iter abs_patches ~f:(fun fault ->
      match Int.Map.find ap_to_feasible_tests Fault.(fault.id) with
      | Some tests ->
          Int.Set.iter tests ~f:(fun i -> fault.Fault.results.(i) <- Fault.SAT)
      | None ->
          () )


let write_results abs_patches test_methods =
  create_dir Config.sprint_debug_dir ;
  let write_result (fault : Fault.t) =
    let result_strs = F.asprintf "%a" Fault.pp_results fault in
    (fault, result_strs)
  in
  let overall_results = List.map abs_patches ~f:write_result in
  Utils.with_file_out "results.csv" ~f:(fun oc ->
      let fmt = F.formatter_of_out_channel oc in
      (* Write headers *)
      F.fprintf fmt "%s\n"
        (String.concat ~sep:","
           ( "abs_patches"
           :: List.map
                ~f:(fun (klass, proc) ->
                  F.asprintf "%a%s" Typ.Name.pp klass (Procname.get_method proc) )
                test_methods ) ) ;
      (* Write each rows *)
      List.iter overall_results ~f:(fun (fault, result_str) ->
          F.fprintf fmt "%s,%s\n" (Fault.id_of fault) result_str ) )


let compute_feasible_fault_combinations abs_patches all_tests : Fault.Set.t list list =
  let all_tests = List.map ~f:(fun (klass, proc) -> Procname.replace_class proc klass) all_tests in
  let module TestMap = PrettyPrintable.MakePPMonoMap (Procname.Set) (Fault.Set) in
  let fault_sat_test_map, covered_tests =
    let add_test tests fault acc =
      match TestMap.find_opt tests acc with
      | Some abs_patches ->
          TestMap.add tests (Fault.Set.add fault abs_patches) acc
      | None ->
          TestMap.add tests (Fault.Set.singleton fault) acc
    in
    List.fold abs_patches ~init:(TestMap.empty, Procname.Set.empty)
      ~f:(fun (acc_map, acc_covered) fault ->
        let sat_tests =
          List.filteri all_tests ~f:(fun i _ ->
              match fault.Fault.results.(i) with SAT -> true | _ -> false )
        in
        let is_no_unsat =
          Array.for_all fault.Fault.results ~f:(function Fault.UnSAT -> false | _ -> true)
        in
        if is_no_unsat && not (List.is_empty sat_tests) then
          let sat_tests = Procname.Set.of_list sat_tests in
          (add_test sat_tests fault acc_map, Procname.Set.union acc_covered sat_tests)
        else (acc_map, acc_covered) )
  in
  L.progress "Fault Sat Test Map: %a@." TestMap.pp fault_sat_test_map ;
  let rec do_worklist ~testmap worklist donelist =
    match worklist with
    | [] ->
        donelist
    | (_, tests_list, tests_to_cover, _) :: rest when Procname.Set.is_empty tests_to_cover ->
        do_worklist ~testmap rest (tests_list :: donelist)
    | ([], _, _, _) :: rest ->
        do_worklist ~testmap rest donelist
    | (tests :: tests_cands, tests_list, tests_to_cover, tests_covered) :: rest ->
        L.progress "worklist size: %d@." (List.length worklist) ;
        let work_tests_not_selected = [(tests_cands, tests_list, tests_to_cover, tests_covered)] in
        let work_tests_selected =
          if Procname.Set.subset tests tests_to_cover && Procname.Set.disjoint tests tests_covered
          then
            [ ( tests_cands
              , tests :: tests_list
              , Procname.Set.diff tests_to_cover tests
              , Procname.Set.union tests tests_covered ) ]
          else []
        in
        do_worklist ~testmap (rest @ work_tests_selected @ work_tests_not_selected) donelist
  in
  if Procname.Set.equal (Procname.Set.of_list all_tests) covered_tests then
    let tests_cands = TestMap.fold (fun tests _ acc -> tests :: acc) fault_sat_test_map [] in
    let init = (tests_cands, [], Procname.Set.of_list all_tests, Procname.Set.empty) in
    let results = do_worklist ~testmap:fault_sat_test_map [init] [] in
    List.map results ~f:(fun tests_list ->
        List.map tests_list ~f:(fun tests ->
            let abs_patches = TestMap.find tests fault_sat_test_map in
            Fault.Set.iter (fun fault -> fault.Fault.status <- Fault.Feasible) abs_patches ;
            abs_patches ) )
  else
    (* TODO: Temporary fix. Some test cannot be analyzed because of dynamically generated code *)
    let partial_abs_patches =
      List.filter abs_patches ~f:(fun Fault.{results} ->
          Array.exists results ~f:(function Fault.SAT -> true | _ -> false) )
      |> Fault.Set.of_list
    in
    Fault.Set.iter (fun fault -> fault.Fault.status <- Fault.Feasible) partial_abs_patches ;
    [[partial_abs_patches]]


let analyze_abs_patches ~get_summary program faulty_procs ~ondemand ~analyze ~reset =
  Profiler.start_event "parse-dynamic-info" ;
  let dyninfo = DynInfo.parse_dyninfo program in
  print_to_file ~dirname:None ~msg:(F.asprintf "%a" DynInfo.pp dyninfo) ~filename:"dyninfo.results" ;
  Profiler.finish_event "parse-dynamic-info" ;
  Profiler.start_event "bottom-up-analysis" ;
  analyze None ;
  Profiler.finish_event "bottom-up-analysis" ;
  if Config.sprint_resolve_recursive then (
    let is_analyzed proc =
      match get_summary proc with
      | Some summaries ->
          let summaries = SpecCheckerSummary.get_disjuncts summaries in
          if List.is_empty summaries then false
          else if List.exists summaries ~f:(fun Domain.{is_incomplete} -> is_incomplete) then false
          else true
      | None ->
          false
    in
    let wto_cg =
      Profiler.start_event "construct-WTO" ;
      if Procname.Set.is_empty faulty_procs then (
        L.d_error "no abs_patches given" ;
        L.exit 12 ) ;
      let entries = Program.get_entries program |> Procname.Set.of_list in
      let relavant_methods =
        let callers_from_target =
          Program.cg_reachables_of program ~forward:false ~reflexive:true faulty_procs
        in
        let callees_from_tests =
          Program.cg_reachables_of program ~forward:true ~reflexive:true entries
        in
        Procname.Set.inter callers_from_target callees_from_tests
        |> Procname.Set.filter (not <<< Program.is_undef_proc program)
        |>
        if Config.sprint_resolve_recursive then Procname.Set.filter (not <<< is_analyzed)
        else fun x -> x
      in
      L.debug L.Analysis L.Quiet "@. - Entry methods : %a@." Procname.Set.pp entries ;
      L.debug L.Analysis L.Quiet "@. - Target methods : %a@." Procname.Set.pp faulty_procs ;
      L.debug L.Analysis L.Quiet "@. - Relevant methods : %a@." Procname.Set.pp relavant_methods ;
      let result = Program.wto_cg program relavant_methods in
      L.debug L.Analysis L.Quiet "[FL] Partition of cg:@.@[<v 2>%a@]@."
        (WeakTopologicalOrder.Partition.pp ~pp_node:(fun fmt proc ->
             F.fprintf fmt "%a@," (Procname.pp_simplified_string ~withclass:true) proc ) )
        result ;
      Profiler.finish_event "construct-WTO" ;
      result
    in
    Profiler.start_event "recursive-analysis" ;
    (* re-analyze recursive procedures if exist *)
    let _visited = ref Procname.Set.empty in
    let ondemand node =
      if is_analyzed node then L.progress "%a is already analyzed!!!@." Procname.pp node
      else (
        L.debug L.Analysis L.Quiet "  - analyze %a@." Procname.pp node ;
        reset ~filter:(fun _ proc -> Procname.equal proc node) () ;
        ondemand node )
    in
    let rec analyze_wto ~is_recursive ~is_first_visit :
        Procname.t WeakTopologicalOrder.Partition.t -> unit = function
      | Empty ->
          ()
      | Node {node; next} when is_recursive ->
          ondemand node ;
          analyze_wto ~is_recursive ~is_first_visit next
      | Node {next} ->
          (* skip analyzing non-recursive methods *)
          analyze_wto ~is_recursive ~is_first_visit next
      | Component {head; rest; next} when is_first_visit ->
          ondemand head ;
          analyze_wto ~is_recursive:true ~is_first_visit:false rest ;
          analyze_wto ~is_recursive:true ~is_first_visit next
      | Component {head; rest; next} ->
          ondemand head ;
          analyze_wto ~is_recursive:true ~is_first_visit rest ;
          analyze_wto ~is_recursive:true next ~is_first_visit
    in
    ( match wto_cg with
    | Empty ->
        L.(die InternalError) "no callees to analyze"
    | Component {next} ->
        analyze_wto ~is_recursive:false ~is_first_visit:true next
    | Node {next} ->
        analyze_wto ~is_recursive:false ~is_first_visit:true next ) ;
    Profiler.finish_event "recursive-analysis" )


let choose_largest_fault abs_patches =
  let init = Fault.Set.choose abs_patches in
  let pdesc = Fault.get_proc_name init |> Program.pdesc_of (Program.from_marshal ()) in
  let rest = Fault.Set.remove init abs_patches in
  Fault.Set.fold
    (fun fault acc ->
      match (acc, fault) with
      | Fault.{desc= WrongExp (e1, _)}, Fault.{desc= WrongExp (e2, _)} -> (
        match (ASTExp.from_IR_exp_opt pdesc e1, ASTExp.from_IR_exp_opt pdesc e2) with
        | Some ae1, Some ae2
          when String.is_substring (ASTExp.to_string ae2) ~substring:(ASTExp.to_string ae1) ->
            fault
        | _ ->
            acc )
      | Fault.{desc= WrongExp _}, _ ->
          acc
      | _, Fault.{desc= WrongExp _} ->
          fault
      | _ ->
          acc )
    rest init


let compute_abs_patches_to_analyze () =
  let all_abs_patches = Fault.from_marshal () in
  let abs_patches_exn_sat, abs_patches_exn_unsat =
    List.partition_tf all_abs_patches ~f:(function
      | Fault.{status= Unreachable | NoExnSat} ->
          false
      | _ ->
          true )
  in
  let number_of_lines abs_patches =
    List.fold abs_patches ~init:Int.Set.empty ~f:(fun acc Fault.{loc} ->
        let line = (Fault.get_location_node loc |> InstrNode.get_loc).Location.line in
        Int.Set.add acc line )
    |> Int.Set.length
  in
  let abs_patches_to_analyze =
    let rec __collect_up_to_X_lines acc : Fault.t list -> Fault.t list = function
      | [] ->
          L.progress "* analyze abs_patches up to %d lines@," (number_of_lines acc) ;
          acc
      | Fault.{score} :: _ as abs_patches ->
          let abs_patches_score, abs_patches_rest =
            List.partition_tf
              ~f:(function Fault.{score= score'} -> Float.equal score score')
              abs_patches
          in
          if number_of_lines (acc @ abs_patches_score) < Config.sprint_sbfl_lines then
            __collect_up_to_X_lines (acc @ abs_patches_score) abs_patches_rest
          else (
            L.progress "* analyze abs_patches up to %d lines@," (number_of_lines acc) ;
            acc )
    in
    __collect_up_to_X_lines [] abs_patches_exn_sat
  in
  L.progress "* unsatisfiable by exn-checker: %d@," (List.length abs_patches_exn_unsat) ;
  L.progress "* abs_patches to analyze: %d@," (List.length abs_patches_to_analyze) ;
  Fault.to_marshal ~path:"abs_patches_to_analyze.data" abs_patches_to_analyze ;
  print_to_file ~dirname:None
    ~msg:(F.asprintf "%a" (Fault.pp_list ~with_sort:true) abs_patches_to_analyze)
    ~filename:"abs_patches_to_analyze" ;
  print_to_file ~dirname:None
    ~msg:(F.asprintf "%a" (Fault.pp_list ~with_sort:true) abs_patches_exn_unsat)
    ~filename:"abs_patches_to_unsat_by_exn" ;
  all_abs_patches


let abs_patches_to_localize_only faulty_locs_list =
  let all_abs_patches = Fault.from_marshal () in
  let correct_line_score =
    match List.rev faulty_locs_list with (score, _) :: _ -> score | _ -> 1.0
  in
  let abs_patches_to_analyze_score =
    List.filter all_abs_patches ~f:(function Fault.{score= score'} ->
        Float.( >= ) score' correct_line_score )
  in
  let abs_patches_to_analyze =
    List.filter abs_patches_to_analyze_score ~f:(function
      | Fault.{status= Unreachable | NoExnSat} ->
          false
      | _ ->
          true )
  in
  L.progress "abs_patches to analyze : %d(all) -> %d(exn-sat)@."
    (List.length abs_patches_to_analyze_score)
    (List.length abs_patches_to_analyze) ;
  Fault.to_marshal ~path:"abs_patches_to_analyze.data" abs_patches_to_analyze ;
  print_to_file ~dirname:None
    ~msg:(F.asprintf "%a" (Fault.pp_list ~with_sort:true) abs_patches_to_analyze)
    ~filename:"abs_patches_to_analyze" ;
  all_abs_patches


let merge_exn_sat_checking_results (fault : Fault.t) =
  Array.fold fault.results ~init:Fault.Unreachable ~f:(fun acc result ->
      match (result, acc) with
      | _, Fault.ExistExnSat ->
          Fault.ExistExnSat
      | Fault.ExnSAT, _ ->
          Fault.ExistExnSat
      | Fault.ExnUnSAT, _ ->
          Fault.NoExnSat
      | Fault.Unexecuted, Fault.Unreachable ->
          Fault.Unreachable
      | Fault.Unexecuted, _ ->
          acc
      | Fault.Unsound, _ | Fault.SAT, _ | Fault.UnSAT, _ | Fault.NoChange, _ ->
          acc )


let revert_sat_results =
  List.iter ~f:(fun fault ->
      match fault.Fault.status with Fault.Feasible -> fault.Fault.status <- ExistExnSat | _ -> () )


let reorder_abs_patches (feasible_abs_patches_combs : Fault.Set.t list list) =
  let visited = ref Fault.Set.empty in
  let fault_with_scores : (Fault.t * float) list =
    List.sort feasible_abs_patches_combs ~compare:(fun comb_a comb_b ->
        List.length comb_a - List.length comb_b )
    |> List.concat_map ~f:(fun comb ->
           if Int.equal (List.length comb) 1 then
             Fault.Set.elements (List.hd_exn comb)
             |> List.map ~f:(fun fault -> (fault, fault.Fault.score))
           else
             let max_scores =
               List.map comb ~f:(fun aps ->
                   Fault.Set.fold (fun ap acc -> Float.max ap.Fault.score acc) aps Float.min_value )
             in
             let max_except_i =
               List.mapi max_scores ~f:(fun i _ ->
                   List.filteri max_scores ~f:(fun j _ -> not (Int.equal i j))
                   |> List.fold ~init:Float.min_value ~f:Float.max )
             in
             match List.zip comb max_except_i with
             | Ok comb_score ->
                 List.concat_map comb_score ~f:(fun (aps, max_score) ->
                     L.progress "aps with %f: %a@." max_score Fault.Set.pp aps ;
                     Fault.Set.elements aps
                     |> List.map ~f:(fun ap -> (ap, Float.min max_score ap.Fault.score)) )
             | _ ->
                 L.(die InternalError) "unmatched" )
    |> List.filter ~f:(fun (ap, _) ->
           if not (Fault.Set.mem ap !visited) then (
             visited := Fault.Set.add ap !visited ;
             true )
           else false )
  in
  List.sort fault_with_scores ~compare:(fun (x, _) (y, _) -> x.Fault.id - y.Fault.id)
  |> List.sort ~compare:(fun (_, a) (_, b) -> Float.compare b a)
  |> List.map ~f:fst


let run get_summary ~reset ~analyze ~ondemand program test_methods =
  let faulty_locs_list =
    if Config.sprint_pfl then SBFL.parse_bug_positions program else SBFL.parse program
  in
  (*********************************
   * 1. Enumerate abstract patches *
   *********************************)
  L.progress "[fault-enumeration]@[<v>@," ;
  Profiler.start_event "fault-enumeration" ;
  let abs_patches =
    if Config.sprint_pfl then (
      let abs_patches = List.concat_map faulty_locs_list ~f:Fault.enumerate in
      Fault.to_marshal abs_patches ;
      Fault.to_marshal ~path:"abs_patches_to_analyze.data" abs_patches ;
      abs_patches )
    else if Config.sprint_exnchecker && not Config.sprint_resolve_recursive then (
      let abs_patches = List.concat_map faulty_locs_list ~f:Fault.enumerate in
      Fault.to_marshal abs_patches ;
      abs_patches )
    else if Config.sprint_exnchecker then Fault.from_marshal ()
    else if Config.sprint_localize_mode then abs_patches_to_localize_only faulty_locs_list
    else compute_abs_patches_to_analyze ()
  in
  L.debug L.Analysis L.Quiet
    "@[<v 2>  -- Test methods:@,  %a@,-- Faulty_locs:@,  %a@,-- Faults:@,  %a@]"
    (Pp.seq (Pp.pair ~fst:Typ.Name.pp ~snd:Procname.pp) ~sep:"\n    ")
    test_methods SBFL.pp faulty_locs_list (Pp.seq Fault.pp ~sep:"\n    ") abs_patches ;
  let faulty_procs =
    List.fold abs_patches ~init:Procname.Set.empty ~f:(fun acc fault ->
        Procname.Set.add (Fault.get_proc_name fault) acc )
  in
  Profiler.finish_event "fault-enumeration" ;
  L.progress "done! @] @." ;
  (******************************
   * 2. Perform static analysis *
   ******************************)
  analyze_abs_patches ~get_summary program faulty_procs ~ondemand ~analyze ~reset ;
  List.iter test_methods ~f:(fun (klass, proc) ->
      if List.is_empty (get_summary_from_test_method get_summary (klass, proc)) then
        L.progress "No state at %a.%s@." Typ.Name.pp klass (Procname.get_method proc) ) ;
  (************************************************
   * 3. Test-SAT checking for each abstract patch *
   ************************************************)
  Profiler.start_event "compute-fault-combination" ;
  L.progress " start to check satisfabilty for reachable abs_patches@." ;
  List.iter abs_patches ~f:(fun fault ->
      (* Returns a list of methods where the fault passes the corresponding tests *)
      List.iteri test_methods ~f:(fun i test_method ->
          match fault.Fault.results.(i) with
          | (Fault.ExnUnSAT | Fault.Unexecuted | Fault.Unsound)
            when (not Config.sprint_exnchecker) && not Config.sprint_pfl ->
              ()
          | _ ->
              let result = validate_fault_by_single_tc get_summary fault test_method in
              fault.Fault.results.(i) <- result ) ) ;
  if not Config.sprint_exnchecker then
    validate_aps_by_nontrivial_summaries get_summary program test_methods abs_patches ;
  (****************************************
   * 4. Solve All-Test-SAT Cover problems *
   ****************************************)
  let fault_combinations =
    if Config.sprint_exnchecker then
      (* TODO: solve All-Test-SAT Cover problems *)
      if Config.sprint_resolve_recursive then
        [ [ List.filter abs_patches ~f:(fun (fault : Fault.t) ->
                fault.status <- merge_exn_sat_checking_results fault ;
                match fault.status with Fault.ExistExnSat -> true | _ -> false )
            |> Fault.Set.of_list ] ]
      else [[Fault.Set.of_list abs_patches]]
    else (
      revert_sat_results abs_patches ;
      let comb = compute_feasible_fault_combinations abs_patches test_methods in
      let analyzed_abs_patches =
        Fault.from_marshal ~path:"abs_patches_to_analyze.data" () |> Fault.Set.of_list
      in
      List.iter abs_patches ~f:(fun fault ->
          match fault.Fault.status with
          | ExistExnSat when Fault.Set.mem fault analyzed_abs_patches ->
              fault.Fault.status <- Fault.Infeasible
          | _ ->
              () ) ;
      comb )
  in
  L.progress " - finish to compute feasible fault combinations (%d)@."
    (List.length fault_combinations) ;
  Profiler.finish_event "compute-fault-combination" ;
  (* print results *)
  Profiler.start_event "print-abs_patches-combinations" ;
  let feasible_fault_combinations_msg =
    List.foldi ~init:"" fault_combinations ~f:(fun i acc abs_patches_list ->
        let pp_abs_patches fmt abs_patches =
          F.fprintf fmt "%a" (Fault.pp_list ~with_sort:true) (Fault.Set.elements abs_patches)
        in
        F.asprintf "================%d-th combination ===========@.%a@.%s" i
          (Pp.seq pp_abs_patches ~sep:"\n------------------------------------------------\n")
          abs_patches_list acc )
  in
  print_to_file ~dirname:None ~msg:feasible_fault_combinations_msg ~filename:"feasible_fault_comb" ;
  Profiler.finish_event "print-abs_patches-combinations" ;
  (********************************************************
   * 5. Reorder Abstract Patches with Test-Satisfiability *
   ********************************************************)
  Profiler.start_event "print-abs_patches" ;
  let feasible_abs_patches = reorder_abs_patches fault_combinations in
  Profiler.start_event "print-abs_patches-feasibles" ;
  let feasible_abs_patches_msg =
    F.asprintf "%a" (Fault.pp_list ~with_sort:false) feasible_abs_patches
  in
  if Config.sprint_exnchecker || Config.sprint_resolve_recursive then
    print_to_file ~dirname:None ~msg:feasible_abs_patches_msg ~filename:"feasible_abs_patches" ;
  Profiler.finish_event "print-abs_patches-feasibles" ;
  (**************************************************
   * 6. Remove Test-SAT equivalent abstract patches *
   **************************************************)
  Profiler.start_event "print-abs_patches-partition-print" ;
  Profiler.start_event "print-abs_patches-partition" ;
  let feasible_abs_patches_list =
    let feasible_abs_patch_set = Fault.Set.of_list feasible_abs_patches in
    Procname.Set.fold
      (fun proc acc ->
        let filename = Procname.to_filename proc ^ ".data" in
        match from_marshal ~dirname:(Some Config.sprint_sat_equal_abs_patches_dir) ~filename with
        | Some abs_patches_set ->
            abs_patches_set @ acc
        | None ->
            acc )
      faulty_procs []
    |> List.filter ~f:(not <<< Fault.Set.disjoint feasible_abs_patch_set)
  in
  Profiler.finish_event "print-abs_patches-partition" ;
  let feasible_fault_partition_msg =
    if Config.sprint_exnchecker then ""
    else
      let pp_fequiv_class fmt (fault, abs_patches) =
        F.fprintf fmt "%s:[%a]" (Fault.id_of fault)
          (Pp.seq ~sep:", " (Pp.of_string ~f:Fault.id_of))
          (Fault.Set.elements abs_patches)
      in
      let largest_and_all =
        List.map feasible_abs_patches_list ~f:(fun abs_patches ->
            (choose_largest_fault abs_patches, abs_patches) )
        |> List.sort ~compare:(fun (f1, _) (f2, _) ->
               Int.of_float (f2.Fault.score *. 1000000.0)
               - Int.of_float (f1.Fault.score *. 1000000.0) )
      in
      let normalized_abs_patches = List.map largest_and_all ~f:fst |> Fault.Set.of_list in
      List.iter abs_patches ~f:(fun fault ->
          if not (Fault.Set.mem fault normalized_abs_patches) then Fault.set_redundant fault ) ;
      F.asprintf "%a" (Pp.seq ~print_env:Pp.text_break pp_fequiv_class) largest_and_all
  in
  Profiler.finish_event "print-abs_patches-partition-print" ;
  Profiler.start_event "print-abs_patches-marshal" ;
  if Config.sprint_exnchecker || Config.sprint_resolve_recursive then Fault.to_marshal abs_patches ;
  Profiler.finish_event "print-abs_patches-marshal" ;
  Profiler.start_event "print-abs_patches-print-to-file" ;
  if Config.sprint_exnchecker || Config.sprint_resolve_recursive then
    print_to_file ~dirname:None ~msg:feasible_fault_partition_msg
      ~filename:"feasible_fault_partition" ;
  Profiler.finish_event "print-abs_patches-print-to-file" ;
  Profiler.pick "print-abs_patches-results" (write_results abs_patches) test_methods ;
  Profiler.finish_event "print-abs_patches" ;
  if Config.sprint_resolve_recursive then Profiler.report ~path:"profile-recursive" ()
  else Profiler.report ~path:"profile" ()
