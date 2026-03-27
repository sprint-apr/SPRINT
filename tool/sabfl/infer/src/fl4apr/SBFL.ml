open! IStd
open! Vocab
module L = Logging

type t = (float * Location.t) list

let pp fmt t =
  F.fprintf fmt "@[<v 2>" ;
  List.iter t ~f:(fun (score, loc) -> F.fprintf fmt "%a (%f)@," Location.pp_file_pos loc score) ;
  F.fprintf fmt "@]"


(** function for parsing ochiai format:
    org.apache.commons.lang3.time$FastDateParserTest#testLANG_831():348;1.0 *)
let[@warning "-32"] parse_gzoltar_line_opt cp_to_floc sbfl_str =
  let[@warning "-8"] [pkg_cls_mthd_line; score_str] = String.split sbfl_str ~on:';' in
  let[@warning "-8"] [pkg_cls_mthd; line_str] = String.split pkg_cls_mthd_line ~on:':' in
  let[@warning "-8"] [pkg_cls; _] = String.split pkg_cls_mthd ~on:'#' in
  let[@warning "-8"] (pkg_str :: class_strs) = String.split pkg_cls ~on:'$' in
  let class_str = String.concat ~sep:"$" class_strs in
  let classpath = String.concat ~sep:"." [pkg_str; class_str] in
  let line = int_of_string line_str in
  let score = float_of_string score_str in
  let floc_opt = String.Map.find cp_to_floc classpath in
  match floc_opt with
  | _ when String.equal "0.0" score_str ->
      None
  | Some Location.{file; col} when not (is_testfile_str (SourceFile.to_string file)) ->
      Some (score, Location.{file; col; line})
  | None when Config.debug_mode ->
      L.progress "[WARNING]: failed to find %s in captured program@." sbfl_str ;
      None
  | _ ->
      None


let parse_line_opt cp_to_floc sbfl_str =
  let[@warning "-8"] [pkg_cls_line; score_str] = String.split sbfl_str ~on:',' in
  let[@warning "-8"] [classpath; line_str] = String.split pkg_cls_line ~on:'#' in
  let line = int_of_string line_str in
  let score = float_of_string score_str in
  let floc_opt = String.Map.find cp_to_floc classpath in
  match floc_opt with
  | Some Location.{file; col} when not (is_testfile_str (SourceFile.to_string file)) ->
      Some (score, Location.{file; col; line})
  | None when Config.debug_mode ->
      L.progress "[WARNING]: failed to find %s in captured program@." sbfl_str ;
      None
  | _ ->
      None


let parse program : t =
  let lines =
    let file = Config.sprint_sbfl_results in
    match Utils.read_file file with
    | Ok (head :: lines) when String.is_prefix head ~prefix:"name" ->
        lines
    | Ok lines ->
        lines
    | Error msg ->
        L.(
          die InternalError "Could not read or parse error report in %s:@\n%s@."
            Config.sprint_sbfl_results msg )
  in
  let lines = List.split_n lines 500 |> fst in
  let all_pdescs : Procdesc.t list =
    Program.all_procs program |> Procname.Set.elements
    |> List.filter_map ~f:(Program.pdesc_of_opt program)
  in
  let cp_to_floc =
    let add_class_if_not_exists acc class_name loc =
      match String.Map.add acc ~key:class_name ~data:loc with `Duplicate -> acc | `Ok acc' -> acc'
    in
    List.fold all_pdescs ~init:String.Map.empty ~f:(fun acc pdesc ->
        match Procdesc.get_proc_name pdesc with
        | Procname.Java mthd -> (
            let class_name = Procname.Java.get_class_name mthd in
            let acc = add_class_if_not_exists acc class_name (Procdesc.get_loc pdesc) in
            match String.lsplit2 ~on:'$' class_name with
            | Some (outer_class, _) ->
                (* Add outer classname too.
                 * e.g., Add org.jsoup.helper.HttpConnection for org.jsoup.helper.HttpConnection$Base *)
                add_class_if_not_exists acc outer_class (Procdesc.get_loc pdesc)
            | None ->
                acc )
        | proc ->
            L.progress "%a is not java method@." Procname.pp proc ;
            acc )
  in
  List.filter_map lines ~f:(parse_line_opt cp_to_floc)


let parse_bug_positions _ : t =
  let lines = ref [] in
  ( match Utils.read_file Config.sprint_bug_positions with
  | Ok text ->
      lines := text
  | Error msg ->
      L.(
        die InternalError "Could not read or parse error report in %s:@\n%s@."
          Config.sprint_bug_positions msg ) ) ;
  let project_id = String.split CommandLineOption.init_work_dir ~on:'/' |> List.last_exn in
  let parse (line : string) =
    match String.split line ~on:'@' with
    | [bug_id; source_path; lines] when String.equal bug_id project_id ->
        let source_file =
          source_file_from_string (SourceFiles.get_all () ~filter:(fun _ -> true)) source_path
        in
        let line_numbers =
          String.split lines ~on:','
          |> List.concat_map ~f:(fun chunk ->
                 match int_of_string_opt chunk with
                 | Some no ->
                     [no]
                 | None when String.is_empty chunk ->
                     []
                 | None when String.contains chunk '-' ->
                     let[@warning "-8"] [src; dst] = String.split chunk ~on:'-' in
                     List.range ~start:`inclusive ~stop:`inclusive (int_of_string src)
                       (int_of_string dst)
                 | None ->
                     raise (Unexpected chunk) )
        in
        List.map line_numbers ~f:(fun line -> (1.0, {(Location.none source_file) with line}))
    | _ ->
        []
  in
  List.concat_map !lines ~f:parse
