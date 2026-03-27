open! IStd
open! Vocab
module Method = Procname.Java
open IOption.Let_syntax

let pgm = lazy (Program.from_marshal ())

module Ty = struct
  let null = Typ.mk_struct (Typ.Name.Java.from_string "sprint.null_type")

  let any_type = Typ.void_star

  let any_primitive_type = Typ.mk_struct (Typ.Name.Java.from_string "sprint.any_primitive_type")

  let is_non_boolean_integer typ =
    Option.value_map ~default:true (Typ.get_ikind_opt typ) ~f:(not <<< Typ.equal_ikind Typ.IBool)


  let is_primitive =
    List.mem ~equal:Typ.equal_ignore_quals
      [Typ.char; Typ.int; Typ.boolean; Typ.uint; Typ.java_char; Typ.long; Typ.float; Typ.double]


  let is_subtype_of ty1 ty2 =
    let open Typ in
    match (ty1, ty2) with
    | _ when Typ.equal ty2 any_primitive_type ->
        if is_primitive ty1 then `Yes else `No
    | _ when is_primitive ty1 && is_primitive ty2 ->
        if Typ.equal ty1 ty2 then `Yes else `No
    | _ when Typ.equal ty2 any_type ->
        `Yes
    | _ -> (
        let ty1', ty2' = (unwrap_if_pointer ty1, unwrap_if_pointer ty2) in
        match (ty1'.desc, ty2'.desc) with
        | Tarray _, Tstruct name ->
            if Typ.Name.equal name Typ.Name.Java.java_lang_object then `Yes else `No
        | _ ->
            Program.type_hierachy !!pgm ty1' ty2' )


  let maybe_subtype_of ty1 ty2 = match is_subtype_of ty1 ty2 with `No -> false | _ -> true

  let get_return_type mthd =
    if Procname.Java.is_constructor mthd then
      mthd |> Procname.Java.get_class_type_name |> Typ.mk_struct |> Typ.mk_ptr
    else Procname.Java.get_return_typ mthd
end

type 'a hole = Empty of Typ.t | Filled of 'a [@@deriving compare, equal]

let any_type_component_hole = Empty Ty.any_type

let any_primitive_type_component_hole = Empty Ty.any_primitive_type

let pp_hole fmt ~pp_value = function
  | Empty ty when Typ.equal ty Ty.any_type ->
      F.fprintf fmt "(ㅁ)"
  | Empty ty ->
      F.fprintf fmt "(%a ㅁ)" (Typ.pp_full Pp.text) ty
  | Filled v ->
      F.fprintf fmt "%a" pp_value v


module Literal = struct
  type t =
    | Integer of IntLit.t
    | NULL
    | Boolean of bool
    | Float of float
    | String of string
    | Class of Ident.name
  [@@deriving equal, compare]

  (** boolean-ness of an integer cannot be decided only with given constant type. *)
  let of_const c =
    match (c : Const.t) with
    | Cint il when IntLit.isnull il ->
        NULL
    | Cint il ->
        Integer il
    | Cfloat f ->
        Float f
    | Cstr s ->
        String s
    | Cclass cls ->
        Class cls
    | Cfun _ ->
        L.die InternalError "Not supported literal type: %a@." (Const.pp Pp.text) c


  let pp fmt = function
    | Integer il ->
        F.fprintf fmt "%a" IntLit.pp il
    | NULL ->
        F.fprintf fmt "null"
    | Boolean b ->
        F.fprintf fmt "%b" b
    | Float f ->
        F.fprintf fmt "%a" F.pp_print_float f
    | String str ->
        F.fprintf fmt "\"%s\"" str
    | Class cls ->
        F.fprintf fmt "%a" Ident.pp_name cls


  let null = NULL

  let lit_true = Boolean true

  let lit_false = Boolean false

  let typeof = function
    | Integer _ ->
        Typ.int
    | NULL ->
        Ty.null
    | Boolean _ ->
        Typ.boolean
    | Float _ ->
        Typ.float
    | String _ ->
        Typ.pointer_to_java_lang_string
    | Class _ ->
        Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Class")
end

type t =
  | Hole of Typ.t
  | Var of Pvar.t * Typ.t
  | Cast of Typ.t * t
  | Literal of Literal.t
  | Unary of Unop.t * t
  | Binary of Binop.t * t * t
  | Ternary of t * t * t
  | NewArray of {elt_typ: Typ.t; length: t}
  | FieldAccess of {base: base; field_hole: Fieldname.t hole}
  | ArrayAccess of {arrexp: t; index: t}
  | MethodCall of {base: base; mthd_hole: Method.t hole; args_hole: t list option}
[@@deriving compare]

and base = StaticAccess of Typ.Name.t hole | DynamicAccess of t

let sort = function
  | Binary (binop, ae1, ae2) ->
      let[@warning "-8"] [ae1; ae2] = List.sort [ae1; ae2] ~compare in
      Binary (binop, ae1, ae2)
  | x ->
      x


let compare (x : t) (y : t) = compare (sort x) (sort y)

let default_of typ =
  let literals : Literal.t list =
    let open Literal in
    match Typ.(typ.desc) with
    | Tvoid ->
        []
    | Tint IBool ->
        [lit_true; lit_false]
    | Tint (IInt | IUShort | ILong | IShort) ->
        [Integer IntLit.zero]
    | Tfloat _ ->
        [Float 0.0]
    | Tptr _ ->
        [NULL]
    | _ ->
        []
  in
  List.map literals ~f:(fun l -> Literal l)


let instanceof =
  Procname.make_java
    ~class_name:(Typ.Name.Java.from_string "FL4APR.Models")
    ~return_type:(Some Typ.boolean) ~method_name:"instanceof" ~parameters:[Typ.void_star]
    ~kind:Static ()
  |> Procname.as_java_exn ~explanation:""


let rec pp fmt = function
  | Var (pvar, _) ->
      F.fprintf fmt "%a" Pvar.pp_value_non_verbose pvar
  | Literal lit ->
      Literal.pp fmt lit
  | Cast (Typ.{desc= Tstruct name}, e) ->
      let unqualified_name =
        String.split_on_chars (Typ.Name.name name) ~on:['.'] |> List.rev |> List.hd_exn
      in
      F.fprintf fmt "(%s) %a" unqualified_name pp e
  | Cast (ty, e) ->
      F.fprintf fmt "(%s) %a" (Typ.to_string ty) pp e
  | NewArray {elt_typ; length} ->
      F.fprintf fmt "new %s[%a]" (Typ.to_string elt_typ) pp length
  | FieldAccess {base; field_hole} ->
      F.fprintf fmt "%a.%a" pp_base base pp_field_hole field_hole
  | ArrayAccess {arrexp: t; index: t} ->
      F.fprintf fmt "%a[%a]" pp arrexp pp index
  | MethodCall {mthd_hole= Filled mthd; args_hole} when Procname.Java.is_constructor mthd ->
      if Config.sprint_synthesis_abspatches then
        F.fprintf fmt "new %s(%a)" (Procname.Java.get_simple_class_name mthd) pp_args_hole args_hole
      else F.fprintf fmt "new %s(%a)" (Procname.Java.get_class_name mthd) pp_args_hole args_hole
  | MethodCall {base; mthd_hole; args_hole} ->
      F.fprintf fmt "%a.%a(%a)" pp_base base pp_method_hole mthd_hole pp_args_hole args_hole
  | Unary (unop, e) ->
      F.fprintf fmt "%s(%a)" (Unop.to_string unop) pp e
  | Binary
      ( binop
      , MethodCall {base= StaticAccess (Filled name); mthd_hole= Filled mthd; args_hole= Some [ap]}
      , _ )
    when Procname.equal (Procname.Java mthd) (Procname.Java instanceof) -> (
    match binop with
    | Binop.Eq ->
        F.fprintf fmt "!(%a instanceof %s)" pp ap (Typ.Name.name name)
    | _ ->
        F.fprintf fmt "%a instanceof %s" pp ap (Typ.Name.name name) )
  | Binary (((Binop.Eq | Binop.Ne) as bo), lhs, Literal (Integer il))
    when Typ.equal (typeof lhs) Typ.boolean && IntLit.iszero il ->
      F.fprintf fmt "%s%a" (if Binop.equal bo Binop.Eq then "!" else "") pp lhs
  | Binary (bop, x, y) ->
      F.fprintf fmt "(%a %s %a)" pp x (Binop.str Pp.text bop) pp y
  | Ternary (c, x, y) ->
      F.fprintf fmt "%a ? %a : %a" pp c pp x pp y
  | Hole ty when Typ.equal ty Ty.any_type ->
      F.fprintf fmt "(ㅁ)"
  | Hole ty ->
      F.fprintf fmt "(%a) ㅁ" (Typ.pp_full Pp.text) ty


and pp_base fmt = function
  | StaticAccess klass_hole ->
      pp_klass_hole fmt klass_hole
  | DynamicAccess base ->
      pp fmt base


and pp_klass_hole =
  pp_hole ~pp_value:(fun fmt klass ->
      F.fprintf fmt "%a"
        (JavaClassName.pp_with_verbosity ~verbose:false)
        (Typ.Name.Java.get_java_class_name_exn klass) )


and pp_field_hole =
  pp_hole ~pp_value:(fun fmt fn -> F.fprintf fmt "%s" (Fieldname.get_field_name fn))


and pp_method_hole =
  pp_hole ~pp_value:(fun fmt mthd -> F.fprintf fmt "%s" (Procname.get_method (Procname.Java mthd)))


and pp_args_hole fmt = function
  | None ->
      F.fprintf fmt "_"
  | Some args ->
      F.fprintf fmt "%a" (Pp.seq pp ~sep:",") args


and typeof = function
  | Var (_, ty) ->
      ty
  | Literal lit ->
      Literal.typeof lit
  | Unary (_, e) ->
      typeof e
  | Cast (ty, _) ->
      ty
  | FieldAccess {field_hole= Filled fn} ->
      (Program.get_fieldinfo !!pgm fn).typ
  | ArrayAccess {arrexp} ->
      Typ.array_elem None (strip_ptr (typeof arrexp))
  | MethodCall {mthd_hole= Filled mthd} ->
      Ty.get_return_type mthd
  | FieldAccess {field_hole= Empty ty} | MethodCall {mthd_hole= Empty ty} ->
      ty
  | Hole ty ->
      ty
  | NewArray {elt_typ} ->
      Typ.mk_array elt_typ
  | Binary (Binop.(Eq | Ne | LAnd | LOr | Lt | Gt | Le | Ge), _, _) ->
      Typ.boolean
  | Binary (Binop.(Div | Mod | Shiftlt | Shiftrt), l, _) ->
      typeof l
  | Binary (Binop.(PlusA (Some _) | MinusA (Some _) | Mult (Some _)), _, _) ->
      Typ.int
  | Binary (Binop.(PlusA None | MinusA None | Mult None), _, _) ->
      Typ.float
  | Ternary (_, e2, _) ->
      typeof e2
  | Binary ((BAnd | BOr | BXor), _, _) ->
      Typ.int
  | Binary ((PlusPI | MinusPI | MinusPP), _, _) as e ->
      L.die InternalError "Cannot compute type of %a@." pp e


let to_string = F.asprintf "%a" pp

let to_yojson e = `String (to_string e)

let equal = [%compare.equal: t]

let mask_token = Literal (String "<MASK>")

let null = Literal Literal.null

let lit_true = Literal Literal.lit_true

let lit_false = Literal Literal.lit_false

let of_var (pv, ty) = Var (pv, ty)

let of_const c = Literal (Literal.of_const c)

let mk_this mthd =
  let this_class = Option.value_exn (Procname.get_class_type_name mthd) in
  of_var (Pvar.mk Mangled.this mthd, Typ.mk_ptr (Typ.mk_struct this_class))


let is_this = function Var (pv, _) -> Pvar.is_this pv | _ -> false

let object_hole = Hole Typ.pointer_to_java_lang_object

let any_type_hole = Hole Ty.any_type

let any_primitive_type_hole = Hole Ty.any_primitive_type

let get_base_exn = function
  | MethodCall {base} | FieldAccess {base} ->
      base
  | e ->
      L.die InternalError "%a has not a base expression" pp e


let get_class_of_base = function
  | StaticAccess (Filled klass) ->
      Some klass
  | StaticAccess (Empty _) as base ->
      L.debug L.Analysis L.Verbose "Could not find base class name of %a" pp_base base ;
      None
  | DynamicAccess e ->
      L.debug L.Analysis L.Verbose "Finding base class name of %a (%a)" pp e (Typ.pp_full Pp.text)
        (typeof e) ;
      e |> typeof |> strip_ptr |> Typ.name


let is_static = function StaticAccess _ -> true | _ -> false

let is_null e = Int.equal (compare e null) 0

let zero = Literal (Integer IntLit.zero)

let is_zero e = Int.equal (compare e zero) 0

let maybe_subtype_of e ~ty =
  match e with
  | MethodCall {mthd_hole= Filled mthd}
    when Procname.Java.is_constructor mthd && Typ.equal ty Ty.null ->
      (* no constructor calls return null *)
      false
  | _ when Typ.equal ty Ty.null ->
      Ty.maybe_subtype_of (typeof e) Typ.pointer_to_java_lang_object
  | Literal NULL ->
      Ty.maybe_subtype_of ty Typ.pointer_to_java_lang_object
  | _ ->
      Ty.maybe_subtype_of (typeof e) ty


let rec is_terminal = function
  | Hole _ ->
      false
  | Var _ | Literal _ ->
      true
  | Cast (_, e) ->
      is_terminal e
  | FieldAccess {base; field_hole= Filled _} ->
      is_base_terminal base
  | FieldAccess _ ->
      false
  | ArrayAccess {arrexp; index} ->
      is_terminal arrexp && is_terminal index
  | MethodCall {base; mthd_hole= Filled _; args_hole= Some args} ->
      List.for_all args ~f:is_terminal && is_base_terminal base
  | MethodCall _ ->
      false
  | Unary (_, e) ->
      is_terminal e
  | Binary (_, b1, b2) ->
      is_terminal b1 && is_terminal b2
  | Ternary (c, t, e) ->
      is_terminal c && is_terminal t && is_terminal e
  | NewArray {length} ->
      is_terminal length


and is_base_terminal = function
  | StaticAccess (Filled _) ->
      true
  | StaticAccess _ ->
      false
  | DynamicAccess base ->
      is_terminal base


let rec is_constant = function
  | Hole _ | Var _ ->
      false
  | Literal _ ->
      true
  | Cast (_, e) ->
      is_constant e
  | Binary (_, l, r) ->
      is_constant l && is_constant r
  | FieldAccess {field_hole= Filled fn} ->
      let Program.{annotations; is_static; initialization} = Program.get_fieldinfo !!pgm fn in
      Annot.Item.is_final annotations && is_static && Option.is_none initialization
  | _ ->
      false


let number_of_holes e =
  let count_hole = function Filled _ -> 0 | _ -> 1 in
  let rec count = function
    | Hole _ ->
        1
    | Var _ | Literal _ ->
        0
    | Cast (_, e) ->
        count e
    | NewArray {length} ->
        count length
    | FieldAccess {base; field_hole} ->
        count_base base + count_hole field_hole
    | ArrayAccess {arrexp; index} ->
        count arrexp + count index
    | MethodCall {base; mthd_hole; args_hole} -> (
        count_base base + count_hole mthd_hole
        +
        match args_hole with
        | Some args ->
            List.fold args ~init:0 ~f:(fun acc arg -> acc + count arg)
        | _ ->
            0 )
    | Unary (_, e') ->
        count e'
    | Binary (_, l, r) ->
        count l + count r
    | Ternary (l, m, r) ->
        count l + count m + count r
  and count_base = function
    | StaticAccess klass_hole ->
        count_hole klass_hole
    | DynamicAccess e ->
        count e
  in
  count e


module Accessibility = struct
  let trans_procname_access : Procname.Java.Access.t -> PredSymb.access = function
    | Default ->
        Default
    | Public ->
        Public
    | Private ->
        Private
    | Protected ->
        Protected
    | Unknown ->
        L.die InternalError "Unknown access"


  let is_accessible_component ~from ~enclosing_class ~access =
    match (access : PredSymb.access) with
    | Public ->
        true
    | Private ->
        Typ.Name.equal from enclosing_class
    | Default ->
        let current_package =
          from |> Typ.Name.Java.get_java_class_name_exn >@ JavaClassName.package
        in
        let component_package =
          Typ.Name.Java.get_java_class_name_exn enclosing_class >@ JavaClassName.package
        in
        String.equal current_package component_package
    | Protected -> (
      match Program.type_hierachy !!pgm (Typ.mk_struct from) (Typ.mk_struct enclosing_class) with
      | `No ->
          false
      | _ ->
          true )


  let is_accessible_method ~from mthd =
    is_accessible_component ~from
      ~enclosing_class:(Procname.Java.get_class_type_name mthd)
      ~access:(Procname.Java.get_access mthd |> trans_procname_access)


  let is_accessible_field ~from fn =
    let Program.{access} = Program.get_fieldinfo !!pgm fn in
    is_accessible_component ~from ~enclosing_class:(Fieldname.get_class_name fn) ~access


  let are_same_package c1 c2 =
    let pkg1 = Typ.Name.Java.get_java_class_name_exn c1 >@ JavaClassName.package in
    let pkg2 = Typ.Name.Java.get_java_class_name_exn c2 >@ JavaClassName.package in
    String.equal pkg1 pkg2


  let base_kind_of : base -> [`Static | `Dynamic | `This] = function
    | StaticAccess _ ->
        `Static
    | DynamicAccess e ->
        if is_this e then `This else `Dynamic


  let is_accessible_component ~base ~from ~target ~access =
    match ((access : PredSymb.access), base_kind_of base) with
    | Public, _ ->
        true
    | Default, _ ->
        are_same_package from target
    | Protected, (`Static | `This) ->
        are_same_package from target
        || not (is_no (Program.type_hierachy !!pgm (Typ.mk_struct from) (Typ.mk_struct target)))
    | Protected, `Dynamic ->
        are_same_package from target
    | Private, (`Static | `This) ->
        Typ.Name.equal from target
    | _ ->
        false


  let is_accessible_method ~base ~from mthd =
    is_accessible_component ~base ~from
      ~target:(Procname.Java.get_class_type_name mthd)
      ~access:(Procname.Java.get_access mthd |> trans_procname_access)


  let is_accessible_field ~base ~from fn =
    is_accessible_component ~from ~base ~target:(Fieldname.get_class_name fn)
      ~access:(Program.get_fieldinfo !!pgm fn).access
end

module Set = Caml.Set.Make (struct
  type nonrec t = t

  let compare = compare
end)

module Converter = struct
  module Hashtbl = Caml.Hashtbl

  exception UnconvertibleExpr of Exp.t

  let varargs : (t, t Array.t) Hashtbl.t = Hashtbl.create 1214

  let cache : (ProcVar.t, t) Hashtbl.t = Hashtbl.create 1214

  module Cache = struct
    let rec find_opt pdesc : Exp.t -> t option =
     fun e ->
      match e with
      | Var id ->
          Hashtbl.find_opt cache (ProcVar.of_id (id, Procdesc.get_proc_name pdesc))
      | UnOp (unop, e, _) ->
          let+ ae = find_opt pdesc e in
          Unary (unop, ae)
      | BinOp (bop, e1, e2) ->
          let+ ae1 = find_opt pdesc e1 and+ ae2 = find_opt pdesc e2 in
          Binary (bop, ae1, ae2)
      | Cast (typ, Const (Cstr "FL4APR_HOLE")) ->
          Some (Hole typ)
      | Cast (ty, e') ->
          let+ ae = find_opt pdesc e' in
          Cast (ty, ae)
      | Exn _ | Closure _ ->
          None
      | Sizeof {dynamic_length} ->
          Option.bind dynamic_length ~f:(find_opt pdesc)
      | Lvar pv ->
          if Pvar.is_frontend_tmp pv then Hashtbl.find_opt cache (ProcVar.of_pvar pv)
          else if Pvar.is_return pv then Some (of_var (pv, Procdesc.get_ret_type pdesc))
          else if not (Pvar.is_global pv) then
            let name_and_types =
              let ProcAttributes.{locals; formals} = Procdesc.get_attributes pdesc in
              formals @ List.map locals ~f:(fun ProcAttributes.{name; typ} -> (name, typ))
            in
            let _, ty =
              List.find_exn name_and_types ~f:(fun (name, _) ->
                  Mangled.equal name (Pvar.get_name pv) )
            in
            Some (of_var (pv, ty))
          else None
      | Lfield (Lvar class_var, fn, _) when Pvar.is_global class_var ->
          (* This is the only case where global pvar appears *)
          let base_class =
            Typ.Name.Java.from_string
              (List.last_exn (String.split (Pvar.to_string class_var) ~on:'$'))
          in
          Some (FieldAccess {base= StaticAccess (Filled base_class); field_hole= Filled fn})
      | Lfield (e, fn, _) ->
          let+ base_aexpr = find_opt pdesc e in
          FieldAccess {base= DynamicAccess base_aexpr; field_hole= Filled fn}
      | Const const ->
          Some (of_const const)
      | Lindex (e1, e2) ->
          let+ base_aexpr = find_opt pdesc e1 and+ index_aexpr = find_opt pdesc e2 in
          ArrayAccess {arrexp= base_aexpr; index= index_aexpr}


    let find pdesc e =
      match find_opt pdesc e with
      | Some aexpr ->
          aexpr
      | None ->
          (* L.progress "Could not convert %a at %a" Exp.pp e Procname.pp (Procdesc.get_proc_name pdesc) ; *)
          raise (UnconvertibleExpr e)


    let add_id pdesc id aexpr =
      Hashtbl.add cache (ProcVar.of_id (id, Procdesc.get_proc_name pdesc)) aexpr
  end

  let rec do_instr pdesc instr =
    try
      match instr with
      | Sil.Load {id; e} ->
          Cache.add_id pdesc id (Cache.find pdesc e)
      | Sil.Store {e1= Lindex (Var id, Const (Cint idx)); e2} ->
          (* Cache.get here may fail if the array is not synthesized exp for varargs. *)
          let varargs_arr = Hashtbl.find varargs (Cache.find pdesc (Var id)) in
          varargs_arr.(IntLit.to_int_exn idx) <- Cache.find pdesc e2
      | Sil.Store {e1= Lvar pv; e2} when Pvar.is_frontend_tmp pv -> (
        match Cache.find pdesc e2 with
        | NewArray {length= Literal (Integer len)} as astexp ->
            (* loading newarr followed by ir-var store indicates var-args assignment *)
            Hashtbl.add varargs astexp (Array.create ~len:(IntLit.to_int_exn len) null) ;
            Hashtbl.add cache (ProcVar.of_pvar pv) astexp
        | astexp ->
            Hashtbl.add cache (ProcVar.of_pvar pv) astexp )
      | Sil.Call ((ret, _), Const (Cfun pname), (e, _) :: (Sizeof {typ}, _) :: _, _, _)
        when Procname.equal pname BuiltinDecl.__cast ->
          Cache.add_id pdesc ret (Cast (typ, Cache.find pdesc e))
      | Sil.Call ((ret, _), Const (Cfun pname), [(arr, _)], _, _)
        when Procname.equal pname BuiltinDecl.__get_array_length ->
          Cache.add_id pdesc ret
            (FieldAccess
               { base= DynamicAccess (Cache.find pdesc arr)
               ; field_hole= Filled Program.array_length_field } )
      | Sil.Call
          ( (ret, _)
          , Const (Cfun pname)
          , (Sizeof {typ= {desc= Tarray {elt}}; dynamic_length= Some length_exp}, _) :: _
          , _
          , _ )
        when Procname.equal pname BuiltinDecl.__new_array ->
          Cache.add_id pdesc ret (NewArray {elt_typ= elt; length= Cache.find pdesc length_exp})
      | Sil.Call (_, Const (Cfun (Procname.Java mthd)), (Var this, _) :: args, _, _)
        when Procname.Java.is_constructor mthd -> (
          let arg_exprs = convert_method_args pdesc args in
          match Cache.find_opt pdesc (Var this) with
          | Some (Var (pv, _)) when Pvar.is_this pv ->
              ()
          | _ ->
              let ae =
                MethodCall
                  { base= StaticAccess (Filled (Procname.Java.get_class_type_name mthd))
                  ; mthd_hole= Filled mthd
                  ; args_hole= Some arg_exprs }
              in
              Cache.add_id pdesc this ae )
      | Sil.Call ((ret, _), Const (Cfun mthd), (Var this, _) :: _, _, _)
        when Procname.equal BuiltinDecl.__cast mthd ->
          (* ret = __cast(this, _) => ap(ret) = ap(this) *)
          Cache.add_id pdesc ret (Cache.find pdesc (Var this))
      | Sil.Call
          ( (ret, _)
          , Const (Cfun mthd)
          , [(Var this, _); (Exp.Sizeof {typ= Typ.{desc= Tstruct name}}, _)]
          , _
          , _ )
        when Procname.equal BuiltinDecl.__instanceof mthd ->
          (* ret = __instanceof(this, _) => ap(ret) = __instanceof(this, typ) *)
          let this_ap = Cache.find pdesc (Var this) in
          let args_hole = Some [this_ap] in
          let ae =
            MethodCall {base= StaticAccess (Filled name); mthd_hole= Filled instanceof; args_hole}
          in
          Cache.add_id pdesc ret ae
      | Sil.Call ((ret, _), Const (Cfun (Procname.Java mthd)), (Var this, _) :: _, _, _)
        when String.equal (Procname.Java.get_method mthd) "append"
             && String.equal "java.lang.StringBuilder" (Procname.Java.get_class_name mthd) ->
          (* ret = append(this, _) => ap(ret) = ap(this) *)
          Cache.add_id pdesc ret (Cache.find pdesc (Var this))
      | Sil.Call ((ret, _), Const (Cfun (Java mthd)), args, _, _) when Procname.Java.is_static mthd
        ->
          let arg_exprs = convert_method_args pdesc args in
          let ae =
            let base_class = Procname.Java.get_class_type_name mthd in
            MethodCall
              { base= StaticAccess (Filled base_class)
              ; mthd_hole= Filled mthd
              ; args_hole= Some arg_exprs }
          in
          Cache.add_id pdesc ret ae
      | Sil.Call ((ret, _), Const (Cfun (Procname.Java mthd)), (Var this, _) :: args, _, _) ->
          let arg_exprs = convert_method_args pdesc args in
          let ae =
            MethodCall
              { base= DynamicAccess (Cache.find pdesc (Var this))
              ; mthd_hole= Filled mthd
              ; args_hole= Some arg_exprs }
          in
          Cache.add_id pdesc ret ae
      | _ ->
          ()
    with _ -> ()


  and convert_method_args pdesc args =
    let f arg =
      let resolved = Cache.find pdesc arg in
      if Hashtbl.mem varargs resolved then Array.to_list (Hashtbl.find varargs resolved)
      else [resolved]
    in
    List.concat_map args ~f:(fun (arg, _) -> f arg)


  let bind_pdesc pdesc =
    let entry = InstrNode.get_first_from (Procdesc.get_start_node pdesc) in
    let rec do_worklist worklist doneset =
      if InstrNode.Set.is_empty worklist then ()
      else
        let work = InstrNode.Set.choose worklist in
        let rest = InstrNode.Set.remove work worklist in
        ignore (do_instr pdesc (InstrNode.get_instr work)) ;
        let next =
          let succs = InstrNode.get_succs work in
          let exns = InstrNode.get_exn work in
          InstrNode.Set.of_list (succs @ exns) |> InstrNode.Set.union rest
        in
        let new_worklist = InstrNode.Set.diff next doneset in
        let new_doneset = InstrNode.Set.add work doneset in
        do_worklist new_worklist new_doneset
    in
    do_worklist (InstrNode.Set.singleton entry) InstrNode.Set.empty


  let from_IR_exp_opt pdesc exp =
    match Cache.find_opt pdesc exp with
    | Some aexp ->
        Some aexp
    | None ->
        bind_pdesc pdesc ;
        Cache.find_opt pdesc exp


  let from_IR_exp pdesc exp =
    match from_IR_exp_opt pdesc exp with
    | Some ae ->
        ae
    | None ->
        L.progress "-- Conversion fails for IR-exp %a in %a@." Exp.pp exp Procname.pp
          (Procdesc.get_proc_name pdesc) ;
        raise (UnconvertibleExpr exp)
end

let rec from_IR_exp = Converter.from_IR_exp

let rec from_IR_exp_opt = Converter.from_IR_exp_opt

let typeof_exp_opt pdesc e =
  let+ ae = from_IR_exp_opt pdesc e in
  typeof ae
