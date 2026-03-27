open! IStd
open Javalib_pack

val load_libraries : jar_filename:string -> unit

val find_library_methods : JBasics.class_name -> JCode.jcode Javalib.jmethod list
