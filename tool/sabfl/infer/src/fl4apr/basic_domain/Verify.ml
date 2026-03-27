open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
open SpecCheckerDomain

exception InvalidDynamicInfo of string

module CheckSummary = struct
  (* TODO: write verifier for summary *)
  let check _proc_desc _disjuncts = ()
end

module CheckNode = struct
  (* TODO: write verifier for node execution *)
  let check _pres _node _instr _posts = ()
end

module CheckInstr = struct
  let check_call contexts instr_node =
    match DynInfo.get_die_info contexts instr_node with
    | AbsBool.V true | AbsBool.Top ->
        raise
          (InvalidDynamicInfo
             (F.asprintf "original post state should exists after call %a, but empty" InstrNode.pp
                instr_node ) )
    | _ ->
        ()


  let check_prune contexts instr_node =
    match DynInfo.get_br_info contexts instr_node with
    | AbsBool.V true ->
        raise
          (InvalidDynamicInfo
             (F.asprintf "original post state should exists after prune %a, but empty" InstrNode.pp
                instr_node ) )
    | _ ->
        ()


  (* Checks whether the analysis results match those from dynamic execution information,
     which checks checks if the original post state exists for the well-executed method call.
        If a mismatch found, halt the analysis and use the safe-pre-pruning results *)
  let check astate node instr posts =
    let instr_node = InstrNode.of_pnode node instr in
    let is_normal_original_execution =
      Domain.is_original astate && not (Domain.is_exceptional astate)
    in
    if (not Config.sprint_exnchecker) && is_normal_original_execution && List.is_empty posts then (
      check_call Domain.(astate.current_ctxs) instr_node ;
      check_prune Domain.(astate.current_ctxs) instr_node )
end

let check_node = CheckNode.check

let check_instr = CheckInstr.check

let check_summary = CheckSummary.check
