open! IStd
module L = Logging
module F = Format

exception TODO of string

exception Unexpected of string

let ( <<< ) f g x = f (g x)

let ( >>> ) f g x = g (f x)

let ( @> ) x f = f (Option.value_exn x)

let ( >@ ) x f = Option.value_exn (f x)

let ( !! ) = Lazy.force

let value_exn x = Option.value_exn x

let is_catch_var pv = String.is_prefix (Pvar.to_string pv) ~prefix:"CatchVar"

let pp_instr = Sil.pp_instr ~print_types:true Pp.text

let equal_instr_except_vflag instr1 instr2 =
  match (instr1, instr2) with
  | _ when Sil.equal_instr instr1 instr2 ->
      true
  | Sil.Call ((id, _), _, _, loc, _), Sil.Call ((id', _), _, _, loc', _) ->
      Ident.equal id id' && Location.equal loc loc'
  | _ ->
      false


let[@warning "-33"] get_line node = Location.(Procdesc.Node.get_loc node).line

let id_func x = x

let is_main_func pname = String.equal "main" (Procname.get_method pname)

let is_call_instr = function Sil.Call _ -> true | _ -> false

let is_virtual_call_instr = function
  | Sil.Call (_, _, _, _, {cf_virtual}) ->
      cf_virtual
  | _ ->
      false


let is_load_instr = function Sil.Load _ -> true | _ -> false

let is_deref_instr = function Sil.Load {id} -> Ident.is_none id | _ -> false

let is_store_instr = function Sil.Store _ -> true | _ -> false

let is_return_instr = function Sil.Store {e1= Lvar pv} when Pvar.is_return pv -> true | _ -> false

let is_prune_instr = function Sil.Prune _ -> true | _ -> false

let is_exn_instr = function Sil.Store {e2= Exp.Exn _} -> true | _ -> false

let is_equal_bo = function Binop.Eq | Binop.Ne -> true | _ -> false

let is_entry_node node =
  Procdesc.Node.equal_nodekind Procdesc.Node.Start_node (Procdesc.Node.get_kind node)


let rec is_nullcheck_exp ~is_true prune_exp =
  match prune_exp with
  | Exp.UnOp (Unop.LNot, e, _) ->
      is_nullcheck_exp e ~is_true:(not is_true)
  | Exp.BinOp (Binop.Eq, e1, e2) when is_true ->
      Exp.is_null_literal e1 || Exp.is_null_literal e2
  | Exp.BinOp (Binop.Ne, e1, e2) when not is_true ->
      Exp.is_null_literal e1 || Exp.is_null_literal e2
  | Exp.Var _ ->
      (* v != null *)
      if is_true then false else true
  | _ ->
      false


let is_nullcheck_instr = function
  | Sil.Prune (bexp, _, _, _) ->
      is_nullcheck_exp ~is_true:true bexp || is_nullcheck_exp ~is_true:false bexp
  | _ ->
      false


let is_string_typ Typ.{desc} =
  match desc with
  | Typ.Tptr (typ, _) -> (
    match Typ.(typ.desc) with
    | Typ.Tstruct name ->
        Typ.Name.equal Typ.Name.Java.java_lang_string name
    | _ ->
        false )
  | _ ->
      false


let extract_load_exp_exn = function
  | Sil.Load {e} ->
      e
  | _ as instr ->
      L.(die InternalError)
        "extract_load_exp_exn is called from non-load instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        instr


let args_of_call_instr_exn = function
  | Sil.Call (_, _, args, _, _) ->
      args
  | _ ->
      L.(die InternalError) "non-call instr is given"


let node_has_same_loc_instr loc node =
  Instrs.exists
    ~f:(fun instr -> Location.equal loc (Sil.location_of_instr instr))
    (Procdesc.Node.get_instrs node)


let get_node_loc_line node = (Procdesc.Node.get_loc node).Location.line

let get_first_instr_of_node node = Instrs.nth_exn (Procdesc.Node.get_instrs node) 0

let equal_node_inter n1 n2 =
  Procdesc.Node.equal n1 n2
  && Procname.equal (Procdesc.Node.get_proc_name n1) (Procdesc.Node.get_proc_name n2)


let instr_get_exps instr =
  Sil.exps_of_instr instr
  @ match instr with Sil.Call (_, _, args, _, _) -> List.map args ~f:fst | _ -> []


let rec combinations ~k ~lst =
  if k <= 0 then [[]]
  else
    match lst with
    | [] ->
        []
    | h :: tl ->
        let with_h = List.map (combinations ~k:(k - 1) ~lst:tl) ~f:(fun l -> h :: l) in
        let without_h = combinations ~k ~lst:tl in
        with_h @ without_h


let equal_typ x y =
  let desc_x, desc_y = (x.Typ.desc, y.Typ.desc) in
  Typ.equal_desc desc_x desc_y


let bigand lst = List.for_all lst ~f:(fun x -> x)

let bigor lst = List.exists lst ~f:(fun x -> x)

let get_instrs = Procdesc.Node.get_instrs

let get_instrs_list n =
  Procdesc.Node.get_instrs n |> Instrs.get_underlying_not_reversed |> Array.to_list


let is_callnode node = Instrs.exists (Procdesc.Node.get_instrs node) ~f:is_call_instr

let is_retnode node =
  let has_retvar = function Exp.Lvar pv when Pvar.is_return pv -> true | _ -> false in
  Instrs.exists (Procdesc.Node.get_instrs node) ~f:(fun instr ->
      List.exists ~f:has_retvar (instr_get_exps instr) )


(** Helpers for manipulating SIL instructions **)
let replace_call_exp_of fexp = function
  | Sil.Call (r, _, args, loc, cflags) ->
      Sil.Call (r, fexp, args, loc, cflags)
  | _ as inst ->
      L.(die InternalError)
        "replace_call_exp_of is applied to non-call-instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        inst


let fexp_from_string_c_fun fname = Exp.Const (Cfun (Procname.from_string_c_fun fname))

let call_instr_info_exn = function
  | Sil.Call ((id, typ), fexp, args, loc, cflags) ->
      ((id, typ), fexp, args, loc, cflags)
  | _ as inst ->
      L.(die InternalError)
        "call_instr_info_exn is applied to non-call-instr: %a"
        (Sil.pp_instr ~print_types:true Pp.text)
        inst


(** printers **)
open ANSITerminal

let step_style = [Bold; white]

let result_style = []

let progress_style = [Bold; white; on_green]

let prerr_step_begin str = prerr_string step_style (F.sprintf "== %s ...@." str)

let prerr_step_done str = prerr_string step_style (F.sprintf "== %s ... done!@.@." str)

let prerr_results str (pp : F.formatter -> 'a -> unit) (value : 'a) : unit =
  prerr_string result_style (F.asprintf "- %s: %a@." str pp value)


let prerr_step_evaluating (str : string) (v : 'a Lazy.t) : 'a =
  prerr_string step_style (F.sprintf "== %s ... @." str) ;
  let value = Lazy.force v in
  prerr_string step_style (F.sprintf "== %s ... done!@.@." str) ;
  value


let to_string_mthd = function
  | Procname.Java mthd ->
      F.asprintf "%s.%s" (Procname.Java.get_class_name mthd) (Procname.Java.get_method mthd)
  | _ as proc ->
      Procname.get_method proc


let create_dir ?(remove = false) dirname =
  match Sys.is_directory dirname with
  | `Yes when remove ->
      Utils.rmtree dirname ;
      Utils.create_dir dirname
  | `Yes ->
      ()
  | `No ->
      Utils.rmtree dirname ;
      Utils.create_dir dirname
  | `Unknown ->
      Utils.create_dir dirname


let print_to_file ?(dirname = None) ~msg ~filename =
  match dirname with
  | Some dirname ->
      create_dir dirname ;
      Utils.with_file_out (dirname ^/ filename) ~f:(fun oc ->
          F.fprintf (F.formatter_of_out_channel oc) "%s@." msg )
  | None ->
      Utils.with_file_out filename ~f:(fun oc ->
          F.fprintf (F.formatter_of_out_channel oc) "%s@." msg )


let to_marshal ?(dirname = None) ~filename obj =
  match dirname with
  | Some dirname ->
      create_dir dirname ;
      Utils.with_file_out (dirname ^/ filename) ~f:(fun oc -> Marshal.to_channel oc obj [])
  | None ->
      Utils.with_file_out filename ~f:(fun oc -> Marshal.to_channel oc obj [])


let from_marshal ?(dirname = None) ~filename =
  let filepath = match dirname with Some dirname -> dirname ^/ filename | None -> filename in
  match Sys.is_file filepath with
  | `Yes ->
      Some (Utils.with_file_in filepath ~f:Marshal.from_channel)
  | _ ->
      None


let prerr_progress () = prerr_string progress_style "@"

let read_json_file_exn filepath =
  match Utils.read_json_file filepath with
  | Ok json ->
      json
  | Error msg ->
      L.(die InternalError "Could not read or parse error report in %s:@\n%s@." filepath msg)


let source_file_from_string files filename =
  let find_or_raise files ~f =
    match List.find files ~f with
    | Some source_file ->
        source_file
    | None ->
        raise
          (Unexpected
             (F.asprintf "Could not find %s from captured files@. - %a@." filename
                (Pp.seq SourceFile.pp) files ) )
  in
  if Char.equal filename.[0] '/' then
    find_or_raise files ~f:(fun source_file ->
        String.(filename = SourceFile.to_abs_path source_file) )
  else
    find_or_raise files ~f:(fun source_file ->
        String.(filename = SourceFile.to_rel_path source_file) )


let join_list list ~joinable ~join ~pp =
  let rec _join acc = function
    | [] ->
        acc
    | work :: rest -> (
        let list_joinable, list_unjoinable = List.partition_tf rest ~f:(joinable work) in
        match list_joinable with
        | [] ->
            _join (work :: acc) list_unjoinable
        | hd :: tl -> (
          try
            let joined = join work hd in
            _join acc ((joined :: list_unjoinable) @ tl)
          with Unexpected msg ->
            L.(die InternalError) "%s@.%a@. joinable @.%a@." msg pp work (Pp.seq pp) list_joinable )
        )
  in
  _join [] list


let list_top_n list ~n ~compare = List.split_n (List.sort list ~compare) n |> fst

let is_double_pointer typ =
  match Typ.(typ.desc) with Tptr (subtyp, _) -> Typ.is_pointer subtyp | _ -> false


let proc_to_json_opt proc =
  let procname = Procname.get_method proc in
  let loc =
    match Procdesc.load proc with Some pdesc -> Procdesc.get_loc pdesc | None -> Location.dummy
  in
  let line = Location.(loc.line) in
  let filepath = Location.(loc.file) |> SourceFile.to_string in
  let result =
    match Procname.get_class_name proc with
    | Some classname ->
        Some
          (`Assoc
            [ ("name", `String procname)
            ; ("class", `String classname)
            ; ("line", `Int line)
            ; ("filepath", `String filepath) ] )
    | None ->
        None
  in
  result


let time_debugger = ref String.Map.empty

let debug_time process_name ~f ~arg =
  let start_time = Unix.gettimeofday () in
  let result = f arg in
  let time = Unix.gettimeofday () -. start_time in
  time_debugger :=
    String.Map.change !time_debugger process_name ~f:(function
      | Some (num_iter, time') ->
          Some (num_iter + 1, time +. time')
      | None ->
          Some (1, time) ) ;
  result


let debug_time_finalize () =
  String.Map.iteri !time_debugger ~f:(fun ~key ~data:(num_iter, time) ->
      L.(debug Analysis Quiet) " - %s : %d, %f@." key num_iter time ) ;
  time_debugger := String.Map.empty


let builtin_procs =
  [ BuiltinDecl.__array_access
  ; BuiltinDecl.__assert_fail
  ; BuiltinDecl.__builtin_va_arg
  ; BuiltinDecl.__builtin_va_copy
  ; BuiltinDecl.__builtin_va_end
  ; BuiltinDecl.__builtin_va_start
  ; BuiltinDecl.__builtin_offsetof
  ; BuiltinDecl.__cast
  ; BuiltinDecl.__cxx_typeid
  ; BuiltinDecl.__delete
  ; BuiltinDecl.__delete_array
  ; BuiltinDecl.__delete_locked_attribute
  ; BuiltinDecl.__exit
  ; BuiltinDecl.__objc_bridge_transfer
  ; BuiltinDecl.__get_array_length
  ; BuiltinDecl.__get_type_of
  ; BuiltinDecl.__global_access
  ; BuiltinDecl.__infer_assume
  ; BuiltinDecl.__infer_fail
  ; BuiltinDecl.__infer_skip
  ; BuiltinDecl.__instanceof
  ; BuiltinDecl.__method_set_ignore_attribute
  ; BuiltinDecl.__new
  ; BuiltinDecl.__new_array
  ; BuiltinDecl.__objc_alloc_no_fail
  ; BuiltinDecl.__objc_dictionary_literal
  ; BuiltinDecl.__placement_delete
  ; BuiltinDecl.__placement_new
  ; BuiltinDecl.__print_value
  ; BuiltinDecl.__require_allocated_array
  ; BuiltinDecl.__set_array_length
  ; BuiltinDecl.__set_file_attribute
  ; BuiltinDecl.__set_locked_attribute
  ; BuiltinDecl.__set_mem_attribute
  ; BuiltinDecl.__set_observer_attribute
  ; BuiltinDecl.__set_unsubscribed_observer_attribute
  ; BuiltinDecl.__set_wont_leak_attribute
  ; BuiltinDecl.__split_get_nth
  ; BuiltinDecl.__throw
  ; BuiltinDecl.__unwrap_exception
  ; BuiltinDecl.abort
  ; BuiltinDecl.exit
  ; BuiltinDecl.free
  ; BuiltinDecl.fscanf
  ; BuiltinDecl.fwscanf
  ; BuiltinDecl.malloc
  ; BuiltinDecl.malloc_no_fail
  ; BuiltinDecl.nsArray_arrayWithObjects
  ; BuiltinDecl.nsArray_arrayWithObjectsCount
  ; BuiltinDecl.objc_autorelease_pool_pop
  ; BuiltinDecl.objc_autorelease_pool_push
  ; BuiltinDecl.objc_cpp_throw
  ; BuiltinDecl.pthread_create
  ; BuiltinDecl.scanf
  ; BuiltinDecl.sscanf
  ; BuiltinDecl.swscanf
  ; BuiltinDecl.vfscanf
  ; BuiltinDecl.vfwscanf
  ; BuiltinDecl.vscanf
  ; BuiltinDecl.vsscanf
  ; BuiltinDecl.vswscanf
  ; BuiltinDecl.vwscanf
  ; BuiltinDecl.wscanf
  ; BuiltinDecl.zero_initialization ]


let is_new pid = Procname.equal pid BuiltinDecl.__new || Procname.equal pid BuiltinDecl.__new_array

let is_builtin_proc callee = List.mem builtin_procs callee ~equal:Procname.equal

let is_lambda = function Procname.Java mthd -> Procname.Java.is_lambda mthd | _ -> false

type three_value = [`Yes | `No | `Unknown] [@@deriving compare]

let is_no = function `No -> true | _ -> false

let is_unknown = function `Unknown -> true | _ -> false

let is_yes = function `Yes -> true | _ -> false

let pp_three_value fmt = function
  | `Yes ->
      F.fprintf fmt "Yes"
  | `No ->
      F.fprintf fmt "No"
  | `Unknown ->
      F.fprintf fmt "Unknown"


let disjunct_three_value x y =
  match (x, y) with
  | `Yes, _ | _, `Yes ->
      `Yes
  | `Unknown, _ | _, `Unknown ->
      `Unknown
  | `No, `No ->
      `No


let join_three_value x y = match (x, y) with `Yes, `Yes -> `Yes | `No, `No -> `No | _ -> `Unknown

let negate_three_value = function `Yes -> `No | `No -> `Yes | `Unknown -> `Unknown

let is_target_node ~line ~cls_str node =
  let node_line = (Procdesc.Node.get_loc node).Location.line in
  match Procdesc.Node.get_proc_name node with
  | Procname.Java mthd ->
      let node_cls = Procname.Java.get_simple_class_name mthd in
      (* L.progress "compare %s:%d and %s:%d@." node_cls node_line cls_str line ; *)
      String.equal node_cls cls_str && Int.equal node_line line
  | _ ->
      Int.equal node_line line


module ThreeValue = struct
  type t = three_value [@@deriving compare]

  let pp = pp_three_value
end

module IRUtils = struct
  let rec fold_expr ~f ~init e =
    match (e : Exp.t) with
    | Var _ | Closure _ | Const _ | Lvar _ | Sizeof _ ->
        f init e
    | Exn e' | UnOp (_, e', _) | Lfield (e', _, _) | Cast (_, e') ->
        fold_expr ~f ~init:(f init e) e'
    | BinOp (_, e1, e2) | Lindex (e1, e2) ->
        fold_expr ~f ~init:(fold_expr ~f ~init:(f init e) e1) e2


  let exprs_of_exp e = fold_expr ~f:(fun acc sub -> sub :: acc) ~init:[] e

  let exps_of_instr instr = Sil.exps_of_instr instr |> List.concat_map ~f:exprs_of_exp
end

module AbsBool = struct
  type t = Bot | V of bool | Top [@@deriving compare]

  let equal = [%compare.equal: t]

  let bottom = Bot

  let is_bottom = function Bot -> true | _ -> false

  let top = Top

  let is_top = function Top -> true | _ -> false

  let leq ~lhs ~rhs =
    phys_equal lhs rhs
    ||
    match (lhs, rhs) with
    | Bot, _ | _, Top ->
        true
    | Top, _ | _, Bot ->
        false
    | V v1, V v2 ->
        Bool.equal v1 v2


  let join a1 a2 =
    match (a1, a2) with
    | Top, _ | _, Top ->
        Top
    | Bot, a | a, Bot ->
        a
    | V v1, V v2 ->
        if Bool.equal v1 v2 then a1 else Top


  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp f = function Bot -> F.fprintf f "Bot" | V v -> Bool.pp f v | Top -> F.fprintf f "Top"

  let v x = V x

  let get = function V v -> Some v | Bot | Top -> None

  let negate = function Bot -> Bot | Top -> Top | V true -> V false | V false -> V true
end

let is_sprint = InferCommand.equal Config.command InferCommand.FL4APR

let debug_html = ref false

let unwrap_if_pointer typ = match typ.Typ.desc with Tptr (typ', _) -> typ' | _ -> typ

let make_field cls_str fld_str = Fieldname.make (Typ.Name.Java.from_string cls_str) fld_str

let collection_classes =
  [ "java.util.Iterator"
  ; "java.util.Collection"
  ; "java.util.AbstractCollection"
  ; "java.util.Enumeration"
  ; "java.util.Collections"
  ; "java.util.ArrayDeque"
  ; "java.util.Deque"
  ; "com.google.common.collect.Lists"
  ; "com.google.common.collect.Sets"
  ; "com.google.common.collect.Queues" ]


let mIsEmptyField = Fieldname.make (Typ.Name.Java.from_string "java.util.Collection") "mIsEmpty"

let mElementsField = Fieldname.make (Typ.Name.Java.from_string "java.util.Collection") "mElements"

let mKeysField = Fieldname.make (Typ.Name.Java.from_string "java.util.Map") "mKeys"

let mMapField =
  Fieldname.make (Typ.Name.Java.from_string "com.google.common.collect.ImmutableMap$Builder") "mMap"


let mValuesField = Fieldname.make (Typ.Name.Java.from_string "java.util.Map") "mValues"

let mConcurrentField =
  Fieldname.make (Typ.Name.Java.from_string "java.util.concurrent.Future") "mResults"


let mRunnableField = Fieldname.make (Typ.Name.Java.from_string "java.lang.Thread") "mRunnable"

let is_model_field =
  List.mem
    [ mConcurrentField
    ; mValuesField
    ; mRunnableField
    ; mIsEmptyField
    ; mElementsField
    ; mKeysField
    ; mMapField ]
    ~equal:Fieldname.equal


let is_single_list l = Int.equal (List.length l) 1

let strip_ptr typ = match Typ.(typ.desc) with Tptr (typ', _) -> typ' | _ -> typ

let is_array typ = match (strip_ptr typ).Typ.desc with Tarray _ -> true | _ -> false

let is_double_array typ =
  match (strip_ptr typ).Typ.desc with Tarray {elt} -> is_array elt | _ -> false


let eventListenerList = "javax.swing.event.EventListenerList"

let is_testfile_str filepath =
  match String.chop_suffix_if_exists filepath ~suffix:".java" |> String.rsplit2 ~on:'/' with
  | Some (path, _)
    when (not (String.is_prefix path ~prefix:"src/test")) && String.is_prefix path ~prefix:"src" ->
      false
  | Some (_, classname) ->
      String.is_suffix classname ~suffix:"Test"
      || String.is_suffix classname ~suffix:"TestCase"
      || String.is_suffix classname ~suffix:"Tests"
      || String.is_prefix classname ~prefix:"Test"
  | None ->
      false


let java_class_from_string class_str =
  match String.substr_index class_str ~pattern:"$$" with
  | Some _ ->
      Typ.Name.Java.from_string "org.mockito.cglib.proxy.Enhancer"
  | None ->
      Typ.Name.Java.from_string class_str


let tmp_ret_id = Ident.create_normal (Ident.string_to_name "FL4APR_tmp_ret") 0

let tmp_arg_id = Ident.create_normal (Ident.string_to_name "FL4APR_arg_ret") 0

let object_typ = Typ.mk_struct Typ.Name.Java.java_lang_object

let primitive_types =
  Typ.Name.Set.of_list
    [ Typ.Name.Java.from_string "java.lang.String"
    ; Typ.Name.Java.from_string "java.lang.Integer"
    ; Typ.Name.Java.from_string "java.lang.StringBuilder"
    ; Typ.Name.Java.from_string "java.lang.StringBuffer" ]


let is_primitive_wrapper name = Typ.Name.Set.mem name primitive_types

let rec is_primitive_wrapper_typ typ =
  match strip_ptr typ with
  | Typ.{desc= Tstruct name} ->
      is_primitive_wrapper name
  | Typ.{desc= Tarray {elt}} ->
      is_primitive_wrapper_typ elt
  | _ ->
      false


let is_exn_handler node =
  Procdesc.Node.equal_nodekind Procdesc.Node.exn_handler_kind (Procdesc.Node.get_kind node)


let read_source_location Location.{file; line} =
  match Utils.read_file (SourceFile.to_rel_path file) with
  | Ok lines ->
      List.nth_exn lines (line - 1)
  | Error error ->
      L.die InternalError "%s@." error


let time_of ~f =
  let before = Unix.gettimeofday () in
  let result = f () in
  (result, Unix.gettimeofday () -. before)
