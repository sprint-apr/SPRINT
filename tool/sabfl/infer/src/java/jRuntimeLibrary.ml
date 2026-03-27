open! IStd
open Javalib_pack

let libraries_class_map = ref JBasics.ClassMap.empty

let interesting_packages = ["java/lang"; "java/util/"]

let load_libraries ~jar_filename =
  let javalib_get_class = Utils.suppress_stderr2 Javalib.get_class in
  let classpath = Javalib.class_path jar_filename in
  let f classmap filename_with_extension =
    match Filename.split_extension filename_with_extension with
    | filename, Some extension
      when String.equal extension "class"
           && List.exists interesting_packages ~f:(fun pkg -> String.is_prefix ~prefix:pkg filename)
      ->
        let cn = JBasics.make_cn (String.map ~f:(function '/' -> '.' | c -> c) filename) in
        JBasics.ClassMap.add cn (javalib_get_class classpath cn) classmap
    | _ ->
        classmap
  in
  libraries_class_map :=
    Utils.zip_fold_filenames ~init:JBasics.ClassMap.empty ~f ~zip_filename:jar_filename


let find_library_methods cn =
  try
    match JBasics.ClassMap.find cn !libraries_class_map with
    | Javalib.JClass _ as jclass ->
        Javalib.get_methods jclass |> JBasics.MethodMap.value_elements
    | _ ->
        []
  with Caml.Not_found -> []
