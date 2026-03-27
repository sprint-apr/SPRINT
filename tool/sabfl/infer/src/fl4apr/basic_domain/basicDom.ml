open! IStd
open! Vocab
module L = Logging
module F = Format

module Result = struct
  type t = Valid | Satisfiable | UnSAT | Unknown

  type result = t

  let to_string_result = function
    | Valid ->
        "Valid"
    | Satisfiable ->
        "Satisfiable"
    | UnSAT ->
        "UnSAT"
    | Unknown ->
        "Unknown"


  let negate_result = function
    | Valid ->
        UnSAT
    | Satisfiable ->
        Satisfiable
    | UnSAT ->
        Valid
    | Unknown ->
        Unknown


  let disjunct r1 r2 =
    match (r1, r2) with
    | Valid, _ | _, Valid ->
        Valid
    | Satisfiable, _ | _, Satisfiable ->
        Satisfiable
    | Unknown, _ | _, Unknown ->
        Unknown
    | UnSAT, UnSAT ->
        UnSAT


  let conjunct r1 r2 =
    match (r1, r2) with
    | _, UnSAT | UnSAT, _ ->
        UnSAT
    | Unknown, _ | _, Unknown ->
        Unknown
    | Satisfiable, _ | _, Satisfiable ->
        Satisfiable
    | Valid, Valid ->
        Valid


  let is_valid = function Valid -> true | _ -> false

  let is_unsat = function UnSAT -> true | _ -> false
end

module AbsTyp = struct
  type t = Exact of Typ.t | Instance of Typ.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt = function
    | Exact typ ->
        F.fprintf fmt "(Exact) %a" (Typ.pp_full Pp.text) typ
    | Instance typ ->
        F.fprintf fmt "(Instance) %a" (Typ.pp_full Pp.text) typ


  module PrintableOrderedAbsTyp = struct
    type nonrec t = t [@@deriving compare]

    let pp = pp
  end

  module Set = AbstractDomain.FiniteSet (PrintableOrderedAbsTyp)

  let pp_opt fmt = function Some abstyp -> pp fmt abstyp | None -> F.fprintf fmt "None"

  let typ_of = function Exact typ | Instance typ -> typ

  let make_instance typ = if Program.is_float typ then Instance Typ.float else Instance typ

  let make_exact typ = if Program.is_float typ then Exact Typ.float else Exact typ

  let typ_from_string class_name =
    Typ.{desc= Tstruct (Typ.Name.Java.from_string class_name); quals= Typ.mk_type_quals ()}


  let null = make_instance Typ.void_star

  let int = make_exact Typ.int

  let float = make_exact Typ.float

  let string = make_exact (typ_from_string "java.lang.String")

  let exn_typ = make_instance (typ_from_string "java.lang.Exception")

  let error_typ = make_instance (typ_from_string "java.lang.Error")

  let check_instance ~lhs ~rhs =
    let lhs, rhs = (typ_of lhs, typ_of rhs) in
    let program = Program.from_marshal () in
    Program.type_hierachy program lhs rhs


  module EqualCache = struct
    include Caml.Map.Make (struct
      type t = Typ.Name.t * Typ.Name.t [@@deriving compare]
    end)

    let __cache = ref empty

    let find name1 name2 =
      let name1, name2 =
        if Typ.Name.compare name1 name2 > 0 then (name1, name2) else (name2, name1)
      in
      find (name1, name2) !__cache


    let add name1 name2 (result : three_value) =
      let name1, name2 =
        if Typ.Name.compare name1 name2 > 0 then (name1, name2) else (name2, name1)
      in
      __cache := add (name1, name2) result !__cache ;
      result
  end

  let check_equal (x, y) =
    let program = Program.from_marshal () in
    match (x, y) with
    | Exact typ1, Exact typ2 ->
        if Typ.equal typ1 typ2 then `Yes else `No
    | (Exact _, Instance typ | Instance typ, Exact _)
      when Program.is_interface_or_abstract_class_typ typ ->
        `Unknown
    | Exact typ1, Instance typ2 ->
        Program.type_hierachy program typ1 typ2
    | Instance typ1, Exact typ2 ->
        Program.type_hierachy program typ2 typ1
    | Instance typ1, Instance typ2 -> (
      match (unwrap_if_pointer typ1, unwrap_if_pointer typ2) with
      | Typ.{desc= Tstruct name1}, Typ.{desc= Tstruct name2}
        when (Program.Class.is_interface program name1 && Program.Class.is_interface program name2)
             || (Program.Class.is_abstract program name1 && Program.Class.is_abstract program name2)
        ->
          (* TODO: fix it *)
          `Unknown
      | Typ.{desc= Tstruct name1}, Typ.{desc= Tstruct name2} -> (
        try EqualCache.find name1 name2
        with Caml.Not_found ->
          let childs1 =
            Program.Class.find_all_children ~reflexive:true program name1 |> Typ.Name.Set.of_list
          in
          let childs2 =
            Program.Class.find_all_children ~reflexive:true program name2 |> Typ.Name.Set.of_list
          in
          let result = if Typ.Name.Set.disjoint childs1 childs2 then `No else `Unknown in
          EqualCache.add name1 name2 result )
      | _ ->
          join_three_value
            (Program.type_hierachy program typ2 typ1)
            (Program.type_hierachy program typ1 typ2) )


  let is_different x y =
    match (x, y) with Some x, Some y -> check_equal (x, y) |> is_no | _ -> false


  let leq ~lhs ~rhs =
    let lhs, rhs = (typ_of lhs, typ_of rhs) in
    let program = Program.from_marshal () in
    match Program.type_hierachy program lhs rhs with `Yes -> true | _ -> false


  let join x y =
    if leq ~lhs:x ~rhs:y then y
    else if leq ~lhs:y ~rhs:x then x
    else (* TODO: find least common superclass *)
      Instance Typ.void_star


  let widen ~prev ~next ~num_iters:_ = join prev next

  let bottom = Exact Typ.void

  let top = Instance Typ.void_star

  let invalid = Exact (Typ.mk_struct (Typ.Name.Java.from_string "invalid"))

  let is_invalid = equal invalid

  let is_bottom = function Exact typ -> Typ.is_void typ | _ -> false

  let is_top = equal top

  let mk_array = function
    | Exact typ ->
        Exact (Typ.mk_array typ)
    | Instance typ ->
        Instance (Typ.mk_array typ)
end

module Allocsite = struct
  include InstrNode

  let of_class ~is_exact cls =
    let class_name = Typ.Name.Java.java_lang_object in
    let return_type = Some (Typ.mk_struct cls |> Typ.mk_ptr) in
    let java_procname =
      if is_exact then
        Procname.make_java ~class_name ~return_type ~method_name:"FL4APR_instance" ~parameters:[]
          ~kind:Static ()
      else
        Procname.make_java ~class_name ~return_type ~method_name:"FL4APR_abstract" ~parameters:[]
          ~kind:Static ()
    in
    dummy_of_proc java_procname


  let of_typ ~is_exact typ =
    let class_name = Typ.Name.Java.java_lang_object in
    let return_type = Some (Typ.mk_ptr typ) in
    let java_procname =
      if is_exact then
        Procname.make_java ~class_name ~return_type ~method_name:"FL4APR_instance" ~parameters:[]
          ~kind:Static ()
      else
        Procname.make_java ~class_name ~return_type ~method_name:"FL4APR_abstract" ~parameters:[]
          ~kind:Static ()
    in
    dummy_of_proc java_procname


  let is_class a =
    let name = get_proc_name a |> Procname.get_method in
    String.is_prefix name ~prefix:"FL4APR"


  let is_abstract a =
    let name = get_proc_name a |> Procname.get_method in
    String.equal name "FL4APR_abstract"


  let is_instance a =
    let name = get_proc_name a |> Procname.get_method in
    String.equal name "FL4APR_instance"


  let pp fmt a =
    match get_proc_name a with
    | Procname.Java mthd when is_class a ->
        let name = strip_ptr (Procname.Java.get_return_typ mthd) in
        if is_abstract a then F.fprintf fmt "(Abstract) %a" (Typ.pp_full Pp.text) name
        else F.fprintf fmt "(Instance) %a" (Typ.pp_full Pp.text) name
    | _ ->
        pp_pretty fmt a


  let get_abstyp_opt a =
    match (get_instr a, get_proc_name a) with
    | Sil.Call (_, Const (Cfun f), [(Exp.Sizeof {typ}, _)], _, _), _ when is_new f ->
        Some (AbsTyp.make_exact typ)
    | Sil.Call ((_, ret_typ), Const (Cfun f), arg_typs, _, {cf_virtual}), _
      when (not cf_virtual)
           &&
           let callee_name = Procname.get_method f in
           String.is_prefix callee_name ~prefix:"new"
           && String.is_suffix callee_name ~suffix:"Set"
           && List.length arg_typs <= 1 ->
        Some (AbsTyp.make_instance ret_typ)
    | _, Procname.Java mthd when is_class a ->
        let typ = Procname.Java.get_return_typ mthd |> strip_ptr in
        if is_abstract a then Some (AbsTyp.make_instance typ) else Some (AbsTyp.make_exact typ)
    | _ ->
        None


  let is_incorrect_loc_field a ~fn =
    match get_abstyp_opt a with
    | Some (AbsTyp.Exact Typ.{desc= Tstruct name}) when not (is_model_field fn) -> (
      match Tenv.lookup (Program.tenv ()) name with
      | Some Struct.{fields} ->
          not (List.exists fields ~f:(fun (fn', _, _) -> Fieldname.equal fn fn'))
      | None ->
          false )
    | Some (AbsTyp.Exact Typ.{desc= Tarray _}) ->
        true
    | _ ->
        false
end

module Context = Context.TestContext

(* module Context = Context.KLimited (struct
     let k = 1
   end) *)

module Contexts = AbstractDomain.FiniteSet (Context)

module Loc = struct
  type t =
    | Id of Context.t * Ident.t * Procname.t
    | Pvar of Context.t * Pvar.t
    | Allocsite of Context.t * Allocsite.t
    | Field of t * Fieldname.t
    | Index of t
    | Null
  [@@deriving compare]

  let hash = Hashtbl.hash

  let rec pp fmt = function
    | Id (ctx, id, p) ->
        F.fprintf fmt "(Id) ctx(%a) %a (%a)" Context.pp ctx Ident.pp id Procname.pp p
    | Pvar (ctx, v) -> (
      match Pvar.get_declaring_function v with
      | Some proc ->
          F.fprintf fmt "(Pvar) ctx(%a) %a (%a)" Context.pp ctx (Pvar.pp Pp.text) v Procname.pp proc
      | None ->
          F.fprintf fmt "(Pvar) ctx(%a) %a" Context.pp ctx (Pvar.pp Pp.text) v )
    | Allocsite (ctx, a) ->
        F.fprintf fmt "(Allocsite) ctx(%a) %a" Context.pp ctx Allocsite.pp a
    | Field (l, f) ->
        F.fprintf fmt "(Field) (%a).(%a)" pp l Fieldname.pp f
    | Index l ->
        F.fprintf fmt "(Index) (%a)[*]" pp l
    | Null ->
        F.fprintf fmt "Null"


  let compare x y =
    match (x, y) with
    | Pvar (_, v1), Pvar (_, v2) when Pvar.is_global v1 && Pvar.is_global v2 ->
        if String.equal (Pvar.to_string v1) (Pvar.to_string v2) then 0 else compare x y
    | _ ->
        compare x y


  let equal = [%compare.equal: t]

  let null = Null

  let is_null loc = equal loc null

  let is_field = function Field _ -> true | Index _ -> true | _ -> false

  let is_allocsite = function Allocsite _ -> true | _ -> false

  let is_pvar = function Pvar _ -> true | _ -> false

  let is_global_pvar = function Pvar (_, pv) -> Pvar.is_global pv | _ -> false

  let of_id ~ctx (id, p) = Id (ctx, id, p)

  let of_pvar ~ctx v = if Pvar.is_global v then Pvar (Context.dummy, v) else Pvar (ctx, v)

  let rec procname_of_opt = function
    | Id (_, _, pid) ->
        Some pid
    | Pvar (_, pv) ->
        Pvar.get_declaring_function pv
    | Allocsite _ ->
        None
    | Field (l, _) ->
        procname_of_opt l
    | Index l ->
        procname_of_opt l
    | Null ->
        None


  let of_allocsite ~ctx a = Allocsite (ctx, a)

  let of_class ~ctx ~is_exact name = of_allocsite (Allocsite.of_class ~is_exact name) ~ctx

  let allocsite_of = function
    | Allocsite (_, a) ->
        a
    | _ as l ->
        L.(die InternalError) "cannot extract allocsite from %a" pp l


  let pvar_of = function
    | Pvar (_, pv) ->
        pv
    | _ as l ->
        L.(die InternalError) "cannot extract pvar from %a" pp l


  let rec compare_without_ctx l1 l2 =
    match (l1, l2) with
    | Id (_, id1, pid1), Id (_, id2, pid2) ->
        if Ident.equal id1 id2 then Procname.compare pid1 pid2 else Ident.compare id1 id2
    | Null, Null ->
        0
    | Allocsite (_, a1), Allocsite (_, a2) ->
        Allocsite.compare a1 a2
    | Pvar (_, v1), Pvar (_, v2) ->
        Pvar.compare v1 v2
    | Field (l1', f1'), Field (l2', f2') ->
        let loc_compare = compare_without_ctx l1' l2' in
        if Int.equal loc_compare 0 then Fieldname.compare f1' f2' else loc_compare
    | Index l1', Index l2' ->
        compare_without_ctx l1' l2'
    | _ ->
        (* compare with construct type -> existing compare *)
        compare l1 l2


  let equal_without_ctx l1 l2 = Int.equal (compare_without_ctx l1 l2) 0

  let rec base_of = function Field (l, _) -> base_of l | Index l -> base_of l | _ as l -> l

  let rec empty_ctx_of =
    let ctx = Context.dummy in
    function
    | Id (_, id, pid) ->
        of_id ~ctx (id, pid)
    | Pvar (_, pv) ->
        of_pvar ~ctx pv
    | Field (l, f) ->
        Field (empty_ctx_of l, f)
    | Index l ->
        Index (empty_ctx_of l)
    | _ as l ->
        l


  let append_field loc ~fn =
    match loc with
    | Null ->
        loc
    | Id _ ->
        L.(die InternalError) "append field %a to id location : %a" Fieldname.pp fn pp loc
    | Allocsite (_, a) when Allocsite.is_incorrect_loc_field a ~fn ->
        Null
    | Index _ ->
        loc
    | _ ->
        Field (loc, fn)


  let append_index loc =
    match loc with
    | Id _ ->
        L.(die InternalError) "append index to id location : %a" pp loc
    | Null ->
        loc
    | Index _ ->
        loc
    | Field (l, _) ->
        Index (base_of l)
    | _ ->
        Index loc


  let detach_field = function Field (base, _) -> base | Index base -> base | _ as loc -> loc

  let rec fields_of = function Field (l, f) -> fields_of l @ [f] | _ -> []
end

module PowLoc = struct
  include AbstractDomain.FiniteSet (Loc)

  let equal = [%compare.equal: t]

  let bot = empty

  let is_bot = is_empty

  let null = singleton Loc.null

  let disjoint x y = is_empty (inter x y)

  let detach_fields locs = fold (fun l -> add (Loc.detach_field l)) locs locs

  let append_fields locs ~fn = map (fun l -> Loc.append_field l ~fn) locs

  let append_indexes locs = map Loc.append_index locs

  let union_indexes locs = fold (fun l -> add (Loc.append_index l)) locs locs
end

module PowProc = struct
  include AbstractDomain.FiniteSet (Procname)

  let equal = [%compare.equal: t]

  let bot = empty

  let is_bot = is_empty
end

module Models = struct
  let class_name = Typ.Name.Java.from_string "FL4APR.Models"

  let lt = Procname.from_string_c_fun "<"

  let gt = Procname.from_string_c_fun ">"

  let leq = Procname.from_string_c_fun "<="

  let geq = Procname.from_string_c_fun ">="

  let eq = Procname.from_string_c_fun "=="

  let ne = Procname.from_string_c_fun "!="

  let neg =
    Procname.make_java ~class_name ~return_type:(Some Typ.boolean) ~method_name:"NOT"
      ~parameters:[Typ.boolean] ~kind:Static ()


  let exn = Procname.from_string_c_fun "EXN"

  let add =
    Procname.make_java ~class_name ~return_type:(Some Typ.int) ~method_name:"+"
      ~parameters:[Typ.int; Typ.int] ~kind:Static ()


  let sub =
    Procname.make_java ~class_name ~return_type:(Some Typ.int) ~method_name:"-"
      ~parameters:[Typ.int; Typ.int] ~kind:Static ()


  let minus = Procname.from_string_c_fun "(-)"

  let field_of fn = Procname.from_string_c_fun (F.asprintf "%a" Fieldname.pp fn)

  let index_of = Procname.from_string_c_fun "[Top]"

  let extern_alloc = Procname.from_string_c_fun "EXTERN"

  let mult = Procname.from_string_c_fun "*"

  let div = Procname.from_string_c_fun "/"

  let hole = Procname.from_string_c_fun "FL4APR_HOLE"

  let cls = Procname.from_string_c_fun "CLS"

  let clone = Procname.from_string_c_fun "CLONE"

  let equals = Procname.from_string_c_fun "EQUALS"

  let append = Procname.from_string_c_fun "APPEND"

  let junitFail = Procname.from_string_c_fun "JUNIT_FAIL"

  let from_binop = function
    | Binop.Eq ->
        eq
    | Binop.Ne ->
        ne
    | Binop.Lt ->
        lt
    | Binop.Gt ->
        gt
    | Binop.Le ->
        leq
    | Binop.Ge ->
        geq
    | _ as binop ->
        raise (Unexpected (F.asprintf "Unsupported binop: %s" (Binop.str Pp.text binop)))
end
