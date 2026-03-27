open! IStd
open! Vocab
module J = Yojson.Basic

type table = (row Array.t[@to_yojson fun arr -> `List (List.map row_to_yojson (Array.to_list arr))])

and row =
  { patch_id: int
  ; patch: Patch.t
  ; fault_id: int
  ; fault_desc: string
  ; sbfl_score: float
  ; rewriting_instr: string
  ; rewriting_succeed: bool
  ; rewritten_source: string option
  ; matched_part: string option
  ; filepath: string
  ; line_range: int * int }
[@@deriving to_yojson, compare]

module SourcePatch = struct
  type t = row

  let compare x y =
    match Location.compare x.patch.Patch.source_location y.patch.Patch.source_location with
    | 0 ->
        Option.compare String.compare x.rewritten_source y.rewritten_source
    | result ->
        result


  let equal = [%compare.equal: t]

  let _org_code = ref Location.Map.empty

  let org_code patch_location =
    match Location.Map.find_opt patch_location !_org_code with
    | Some code ->
        code
    | None ->
        let read_nth_line filename n =
          let command = Printf.sprintf "sed -n '%dp' %s" n filename in
          let channel = Unix.open_process_in command in
          let line = input_line channel in
          ignore (Unix.close_process_in channel) ;
          line
        in
        let source_path = SourceFile.to_rel_path patch_location.Location.file in
        let result = read_nth_line source_path patch_location.Location.line in
        _org_code := Location.Map.add patch_location result !_org_code ;
        result


  let to_yojson t : Yojson.Safe.t =
    let patch_location = t.patch.Patch.source_location in
    let source_path = SourceFile.to_rel_path patch_location.Location.file in
    let line = patch_location.Location.line in
    let bug_id = Unix.getcwd () |> Filename.basename in
    let patch_code = Option.value_exn t.rewritten_source in
    `Assoc
      [ ("bug_id", `String bug_id)
      ; ("source_path", `String source_path)
      ; ("line_from", `Int line)
      ; ("line_to", `Int line)
      ; ("patch_code", `String patch_code) ]
end

module SourcePatches = Caml.Set.Make (SourcePatch)

type fault = Fault.t

let fault_to_yojson fault = `String (F.asprintf "%a" Fault.pp_full fault)

type overall_status =
  { running_environment: running_environment
  ; exitcode: int
  ; stacktrace: string option
  ; pruned_abs_patches: int
  ; ir_patches: int
  ; satisifiable: int
  ; unsatisifiable: int
  ; out_of_scope: int
  ; converted: int
  ; patch_template_status: patch_template_status
  ; abs_patches: fault list }
[@@deriving to_yojson]

and running_environment =
  {date: string; timeout: int; pfl_mode: bool; do_static_prune: bool; do_patch_conversion: bool}
[@@deriving to_yojson]

and patch_template_status = (string * int) list [@@deriving to_yojson]

let initial_overall_status =
  { running_environment=
      { date= Time.now () |> Time.to_string
      ; timeout= Config.sprint_synthesis_timeout
      ; pfl_mode= Config.sprint_pfl
      ; do_static_prune= Config.sprint_static_prune
      ; do_patch_conversion= Config.sprint_patch_conversion }
  ; exitcode= 0
  ; stacktrace= None
  ; pruned_abs_patches= 0
  ; ir_patches= 0
  ; satisifiable= 0
  ; unsatisifiable= 0
  ; out_of_scope= 0
  ; converted= 0
  ; patch_template_status= []
  ; abs_patches= [] }


let mk_row ~(fault : Fault.t) ~(patch : Patch.t) =
  let program = Program.from_marshal () in
  let pdesc = Program.pdesc_of program patch.procname in
  let start = Procdesc.get_start_node pdesc |> Procdesc.Node.get_loc in
  let exit = Procdesc.get_exit_node pdesc |> Procdesc.Node.get_loc in
  { patch_id= patch.id
  ; patch
  ; fault_id= fault.id
  ; fault_desc= Fault.description_name fault
  ; sbfl_score= fault.score
  ; rewriting_instr= ""
  ; rewriting_succeed= false
  ; rewritten_source= None
  ; matched_part= None
  ; filepath= SourceFile.to_rel_path patch.Patch.source_location.file
  ; line_range= (start.line, exit.line) }


let acc_patch_status = ref Synthesizer.M.empty

let compute_overall_status ?(exitcode = 0) ?(stacktrace = None) abs_patches table =
  let rows = Array.to_list table in
  let converted =
    List.length (List.filter rows ~f:(fun {rewriting_succeed} -> rewriting_succeed))
  in
  { initial_overall_status with
    exitcode
  ; stacktrace
  ; pruned_abs_patches= List.length abs_patches
  ; ir_patches= Array.length table
  ; converted
  ; patch_template_status=
      Synthesizer.M.bindings !acc_patch_status |> List.Assoc.map ~f:Patch.Set.cardinal }


type pre =
  { program: Program.t
  ; dyninfo: unit
  ; abs_patches: fault list
  ; get_summary: Procname.t -> SpecCheckerSummary.t option }

type work = {id: string; func: pre -> table -> table; exitcode: int}

let n_patches = ref 0

let synthesis_ir_patches fault =
  let Synthesizer.{patches_per_template}, _ =
    Synthesizer.generate_patches ~abstract_mode:Config.sprint_synthesis_abspatches fault
  in
  let _ =
    acc_patch_status :=
      Synthesizer.M.union
        (fun _ s1 s2 -> Some (Patch.Set.union s1 s2))
        !acc_patch_status patches_per_template
  in
  Synthesizer.M.bindings patches_per_template
  |> List.concat_map ~f:(fun (_, patches) ->
         if Patch.Set.is_empty patches then []
         else
           let patches =
             if Config.sprint_baseline || Config.sprint_line_level then Patch.Set.elements patches
             else StaticFilter.filter_patches fault (Patch.Set.elements patches)
           in
           List.sort patches ~compare:(fun x y -> Int.compare x.Patch.id y.Patch.id)
           |> List.map ~f:(fun patch -> mk_row ~fault ~patch) )
  |> List.to_array


let convert_ir_patches =
  n_patches := 0 ;
  let do_row row =
    let conversions = Array.of_list (Rewriter.apply row.patch) in
    (* L.progress "convert (%d) %a@." row.fault_id Patch.pp row.patch ; *)
    Array.map conversions ~f:(fun app ->
        match app.Rewriter.result with
        | Ok {rewritten_source; matched_part} ->
            { row with
              rewriting_instr= app.Rewriter.cmd
            ; rewriting_succeed= true
            ; rewritten_source= Some rewritten_source
            ; matched_part= Some matched_part }
        | Error _ ->
            {row with rewriting_instr= app.Rewriter.cmd; rewriting_succeed= false} )
  in
  fun patches ->
    Array.concat_map patches ~f:(fun row ->
        if !n_patches > 100000 then [||]
        else
          let results : row array = do_row row in
          n_patches :=
            !n_patches + Array.count results ~f:(fun {rewriting_succeed} -> rewriting_succeed) ;
          L.progress "%d patches enumerated@." !n_patches ;
          results )


let duplicate_prune_abs_patches abs_patches =
  List.concat_map abs_patches ~f:(fun fault ->
      match fault with
      | Fault.{org_instr= Sil.Prune _; desc= WrongExp (BinOp (binop, e1, e2), typ)} ->
          let binop_neg = Option.value_exn (Binop.negate binop) in
          [fault; Fault.{fault with desc= WrongExp (BinOp (binop_neg, e1, e2), typ)}]
      | _ ->
          [fault] )


let execute ~program ~get_summary ~abs_patches =
  let abs_patches = duplicate_prune_abs_patches abs_patches in
  if Config.sprint_line_level || Config.sprint_baseline then ()
  else ignore (DynInfo.parse_dyninfo program) ;
  (* For debugging purpose *)
  let do_fault acc fault =
    if Array.count acc ~f:(fun {rewriting_succeed} -> rewriting_succeed) > 100000 then acc
    else
      let patches = synthesis_ir_patches fault in
      let patches_converted = convert_ir_patches patches in
      Array.append acc patches_converted
  in
  let print_results table' =
    Utils.with_file_out
      ~f:(fun oc ->
        let patches =
          Array.to_list table'
          |> List.fold ~init:([], SourcePatches.empty) ~f:(fun (acc, acc_set) patch ->
                 if SourcePatches.mem patch acc_set then (acc, acc_set)
                 else (acc @ [patch], SourcePatches.add patch acc_set) )
          |> fst
        in
        let patch_json_list =
          List.filter_map patches ~f:(fun row ->
              if Config.sprint_synthesis_abspatches then Some (row_to_yojson row)
              else if Option.is_none row.rewritten_source then None
              else Some (SourcePatch.to_yojson row) )
        in
        Yojson.Safe.to_channel oc (`List patch_json_list) )
      (if Config.sprint_synthesis_abspatches then "convert_ir_patches.json" else "patches.json") ;
    table'
  in
  List.fold abs_patches ~init:[||] ~f:do_fault
  |> print_results
  |> compute_overall_status abs_patches
  |> function
  | ({exitcode} : overall_status) as status ->
      Utils.with_file_out
        ~f:(fun oc ->
          Yojson.Safe.pretty_print (F.formatter_of_out_channel oc) (overall_status_to_yojson status)
          )
        "overall_status.json" ;
      L.exit exitcode
