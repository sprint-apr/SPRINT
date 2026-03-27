open! IStd
open! Vocab
module L = Logging
module M = PrettyPrintable.MakePPMap (String)

type status =
  { bug_id: string
  ; fault: Fault.t
  ; num_patches: int
  ; start_time: Time_ns.t
  ; end_time: Time_ns.t
  ; patches_per_template: Patch.Set.t M.t }

let pp_status fmt {bug_id; fault; num_patches; start_time; end_time; patches_per_template} =
  F.fprintf fmt
    "@[<v>Bug ID: %s@,\
     Target Fault: %a@,\
     # Total Patches: %d@,\
     Start Time: %a@,\
     End Time: %a (%f sec. elapsed)@,\
     Generated patches per fault:@,\
     @[<v>%a@]@]"
    bug_id Fault.pp fault num_patches Time_ns.pp start_time Time_ns.pp end_time
    (Time_ns.diff end_time start_time |> Time_ns.Span.to_sec)
    (M.pp ~pp_value:Patch.Set.pp) patches_per_template


let generate_patches ~abstract_mode fault =
  let start_time = Time_ns.now () in
  let patches_per_template =
    let templates =
      if abstract_mode then PatchTemplate.get_abstract_templates ()
      else PatchTemplate.get_templates ()
    in
    ( match Config.sprint_synthesizer_template with
    | Some template ->
        List.filter templates ~f:(function
          | PatchTemplate.{name} when String.equal name template ->
              true
          | _ ->
              false )
    | _ ->
        templates )
    |> List.fold ~init:M.empty ~f:(fun acc PatchTemplate.{name; generate} ->
           M.add name (Patch.Set.of_list (generate fault)) acc )
  in
  let end_time = Time_ns.now () in
  let status =
    { bug_id= Unix.getcwd () |> Filename.basename
    ; fault
    ; num_patches=
        M.fold
          (fun _ patches acc -> Patch.Set.union acc patches)
          patches_per_template Patch.Set.empty
        |> Patch.Set.cardinal
    ; start_time
    ; end_time
    ; patches_per_template }
  in
  L.debug L.Analysis L.Verbose "== Patch Synthesis Status ==@.%a@." pp_status status ;
  ( status
  , M.fold (fun _ patches acc -> Patch.Set.union patches acc) patches_per_template Patch.Set.empty
    |> Patch.Set.elements )


let generate_patches_on_given_location ~abstract_mode location =
  let abs_patches = Fault.enumerate location in
  List.concat_map abs_patches ~f:(snd <<< generate_patches ~abstract_mode)
