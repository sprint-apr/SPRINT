open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode
module Allocsite = BasicDom.Allocsite
module Result = BasicDom.Result
module Models = BasicDom.Models
module AbsTyp = BasicDom.AbsTyp
module Context = BasicDom.Context
module Contexts = BasicDom.Contexts

module Counter (Key : PrettyPrintable.PrintableOrderedType) = struct
  include PrettyPrintable.MakePPMonoMap (Key) (Int)

  let _counter = ref empty

  let get k =
    match find_opt k !_counter with
    | Some cnt ->
        _counter := add k (cnt + 1) !_counter ;
        cnt
    | None ->
        _counter := add k 1 !_counter ;
        0
end

module NodeSymbol = struct
  type t = Allocsite.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt instr_node =
    let loc = InstrNode.get_loc instr_node in
    let instr_str =
      F.asprintf "%a" (Sil.pp_instr ~print_types:false Pp.text) (InstrNode.get_instr instr_node)
      |> String.length
    in
    if Location.equal Location.dummy loc then
      match InstrNode.get_proc_name instr_node with
      | Procname.Java mthd when Procname.Java.is_constructor mthd ->
          F.fprintf fmt "%s (%d)" (Procname.Java.get_simple_class_name mthd) instr_str
      | proc_name ->
          F.fprintf fmt "%s (%d)" (Procname.get_method proc_name) instr_str
    else F.fprintf fmt "%a (%d)" Location.pp_line loc instr_str


  let make node : t = node

  let dummy : t = InstrNode.dummy

  let get_abstyp_opt = Allocsite.get_abstyp_opt
end

module SymbolCore = struct
  type access = Field of Fieldname.t | Index of IntLit.t [@@deriving compare]

  type base = Global of Pvar.t * access | Param of (int * (Pvar.t[@compare.ignore]))
  [@@deriving compare]

  let pp_access fmt = function
    | Field fn ->
        F.fprintf fmt ".%s" (Fieldname.to_simplified_string fn)
    | Index i ->
        F.fprintf fmt "[%a]" IntLit.pp i


  let pp_base fmt = function
    | Global (pv, access) ->
        F.fprintf fmt "G$(%a%a)" (Pvar.pp Pp.text) pv pp_access access
    | Param (i, pv) -> (
      match Pvar.get_declaring_function pv with
      | Some proc ->
          F.fprintf fmt "P(%d%a_%s)" i (Pvar.pp Pp.text) pv (Procname.get_method proc)
      | None ->
          F.fprintf fmt "P(%d%a)" i (Pvar.pp Pp.text) pv )


  type t =
    | Path of base * access list
    | Last of base * access list
    | Abstract of base * access list * access
  [@@deriving compare]

  let pp_access fmt = function
    | Field fn ->
        F.fprintf fmt ".%s" (Fieldname.to_simplified_string fn)
    | Index i ->
        F.fprintf fmt "[%a]" IntLit.pp i


  let pp_base fmt = function
    | Global (pv, access) ->
        F.fprintf fmt "G$(%a%a)" (Pvar.pp Pp.text) pv pp_access access
    | Param (i, pv) -> (
      match Pvar.get_declaring_function pv with
      | Some proc ->
          F.fprintf fmt "P(%d%a_%s)" i (Pvar.pp Pp.text) pv (Procname.get_method proc)
      | None ->
          F.fprintf fmt "P(%d%a)" i (Pvar.pp Pp.text) pv )


  let pp fmt : t -> unit = function
    | Path (base, accesses) ->
        F.fprintf fmt "$P(%a%a)" pp_base base (Pp.seq pp_access) accesses
    | Last (base, accesses) ->
        F.fprintf fmt "$L(%a%a)" pp_base base (Pp.seq pp_access) accesses
    | Abstract (base, accesses, access) ->
        F.fprintf fmt "$A(%a%a*%a)" pp_base base (Pp.seq pp_access) accesses pp_access access


  let equal = [%compare.equal: t]

  let equal_base = [%compare.equal: base]

  let equal_access = [%compare.equal: access]

  let sub_accesses accesses : access list list =
    match List.rev accesses with
    | _ :: tl ->
        List.fold (List.rev tl) ~init:([[]], []) ~f:(fun (acc, accesses') access ->
            let new_accesses = accesses' @ [access] in
            (new_accesses :: acc, new_accesses) )
        |> fst
    | [] ->
        []


  let sub_symbols = function
    | Path (base, accesses) | Last (base, accesses) ->
        List.map (sub_accesses accesses) ~f:(fun sub_accesses -> Path (base, sub_accesses))
    | Abstract (base, accesses, _) ->
        Last (base, accesses)
        :: List.map (sub_accesses accesses) ~f:(fun sub_accesses -> Path (base, sub_accesses))


  let base_of = function Path (base, _) | Last (base, _) | Abstract (base, _, _) -> base

  let is_this t = match base_of t with Param (_, pv) -> Pvar.is_this pv | _ -> false

  let is_global t = match base_of t with Global _ -> true | _ -> false

  let is_param t = match base_of t with Param _ -> true | _ -> false

  let make_global pv fn = Path (Global (pv, Field fn), [])

  let of_pvar i pv = Path (Param (i, pv), [])

  let is_last_access accs access =
    match (access, accs) with
    | _ when List.length accs > 3 ->
        true
    | _, Index _ :: Field fn :: _ -> (
      match Program.get_field_typ_opt fn with None -> true | Some typ -> not (is_double_array typ) )
    | _, Index _ :: _ ->
        true
    | Index _, _ ->
        false
    | Field fn, _
      when List.mem ["mKeys"; "mValues"] (Fieldname.get_field_name fn) ~equal:String.equal ->
        true
    | _, Field fn :: _ when List.mem ["mElements"] (Fieldname.get_field_name fn) ~equal:String.equal
      ->
        true
    | Field fn, _ when List.mem accs (Field fn) ~equal:equal_access ->
        true
    | Field fn, _ when Program.is_innerclass_field fn ->
        true
    | Field fn, _ when String.is_suffix (Fieldname.get_field_name fn) ~suffix:"Type" ->
        true
    | Field fn, _ -> (
      match Program.get_field_typ_opt fn with
      | (Some Typ.{desc= Tstruct field_name} | Some Typ.{desc= Tptr ({desc= Tstruct field_name}, _)})
        when Typ.Name.equal field_name (Fieldname.get_class_name fn) ->
          true
      | _ ->
          false )


  let append_access access = function
    | Path (base, accs) when is_last_access accs access ->
        Last (base, accs @ [access])
    | Path (base, accs) ->
        Path (base, accs @ [access])
    | Last (base, accs) ->
        Abstract (base, accs, access)
    | Abstract (base, accs, _) ->
        Abstract (base, accs, access)


  let append_field ~fn = append_access (Field fn)

  let append_index ~index = append_access (Index index)

  let rec default_typ_opt_of_accesses accesses =
    match List.rev accesses with
    | [] ->
        None
    | Field fn :: _ ->
        Program.get_field_typ_opt fn |> Option.map ~f:AbsTyp.make_instance
    | Index _ :: accesses' -> (
      match default_typ_opt_of_accesses (List.rev accesses') with
      | Some (AbsTyp.Instance typ) ->
          Some (AbsTyp.Instance (Typ.array_elem (Some Typ.void_star) typ))
      | Some (AbsTyp.Exact typ) ->
          Some (AbsTyp.Exact (Typ.array_elem (Some Typ.void_star) typ))
      | None ->
          None )


  let rec default_typ_opt : t -> AbsTyp.t option = function
    | Path (Param (_, pv), []) ->
        Program.get_pvar_typ_opt pv |> Option.map ~f:AbsTyp.make_instance
    | Path (Global (_, Field fn), []) ->
        Program.get_field_typ_opt fn |> Option.map ~f:AbsTyp.make_instance
    | Path (Global (_, Index _), []) ->
        None
    | Path (_, accs) | Last (_, accs) ->
        default_typ_opt_of_accesses accs
    | Abstract (_, _, Field _) ->
        Some AbsTyp.top
    | Abstract (_, _, Index _) ->
        Some AbsTyp.top


  let endswith fn = function
    | Abstract (_, _, Field fn') ->
        Fieldname.equal fn fn'
    | Path (_, accs) | Last (_, accs) -> (
      match List.rev accs with Field fn' :: _ -> Fieldname.equal fn fn' | _ -> false )
    | Abstract (_, _, Index _) ->
        false
end

module Symbol = struct
  include SymbolCore
  module Set = AbstractDomain.FiniteSet (SymbolCore)
end

module FloatLit = struct
  type t = FLit of float | FNaN | FInf [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt = function
    | FLit float ->
        F.fprintf fmt "%f" float
    | FNaN ->
        F.fprintf fmt "NaN"
    | FInf ->
        F.fprintf fmt "FInf"


  let of_float x = if Float.is_nan x then FNaN else if Float.is_inf x then FInf else FLit x

  let nan = FNaN

  let inf = FInf

  let is_normal = function FLit _ -> true | _ -> false

  let zero = FLit 0.0
end

module SymVal = struct
  type absval = AbsFloat | AbsString | AbsHeap [@@deriving compare]

  let pp_absval fmt = function
    | AbsFloat ->
        F.fprintf fmt "AbsFloat"
    | AbsString ->
        F.fprintf fmt "AbsString"
    | AbsHeap ->
        F.fprintf fmt "AbsHeap"


  type t =
    (* Not strong updatable, but concrete values *)
    | VInt of IntLit.t
    | VFloat of FloatLit.t
    | VString of string
    | VNull
    (* strong updatable (i.e., unique) values *)
    | VSymbol of Symbol.t
    | VFreshSymbol of Procname.t * NodeSymbol.t
    (* functions of values *)
    | VInjFunction of (Procname.t * t list)
    | VFunction of (Procname.t * t list)
    | VAbsFun of (Procname.t * t list)
    (* abstract values *)
    | VHeap of NodeSymbol.t
    | VAbstract of absval
    | VTopPrimitive
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let rec pp fmt = function
    | VInt intlit ->
        F.fprintf fmt "%a" IntLit.pp intlit
    | VFloat flit ->
        F.fprintf fmt "%a" FloatLit.pp flit
    | VString str ->
        F.fprintf fmt "%s" str
    | VNull ->
        F.fprintf fmt "Null"
    | VHeap n ->
        F.fprintf fmt "%a" NodeSymbol.pp n
    | VSymbol s ->
        F.fprintf fmt "%a" Symbol.pp s
    | VInjFunction (f, args) ->
        F.fprintf fmt "InjFun %s(%a)" (Procname.get_method f) (Pp.seq pp ~sep:",") args
    | VFunction (f, args) ->
        F.fprintf fmt "Fun %s(%a)" (Procname.get_method f) (Pp.seq pp ~sep:",") args
    | VAbsFun (f, args) ->
        F.fprintf fmt "AbsFun %s(%a)" (Procname.get_method f) (Pp.seq pp ~sep:",") args
    | VFreshSymbol (f, ext) ->
        F.fprintf fmt "Fresh (%s, %a)" (Procname.get_method f) NodeSymbol.pp ext
    | VAbstract absval ->
        F.fprintf fmt "%a" pp_absval absval
    | VTopPrimitive ->
        F.fprintf fmt "Top"


  (** values **)
  let null = VNull

  let zero = VInt IntLit.zero

  let one = VInt IntLit.one

  let top_primitive = VTopPrimitive

  let cleene_star = VAbstract AbsString

  let hole_symbol = VFreshSymbol (Models.hole, NodeSymbol.dummy)

  let unknown = VAbstract AbsHeap

  (** Queries **)

  let is_top_primitive = function VTopPrimitive -> true | _ -> false

  let is_primitive = function
    | VInt _ | VFloat _ | VString _ | VAbstract AbsFloat | VAbstract AbsString | VTopPrimitive ->
        true
    | _ ->
        false


  (* check whether a value is abstract.
     abs_value = v is always SAT, thus it could not have any contraints such as v == x *)
  let rec is_abstract = function
    | VAbstract _ | VTopPrimitive ->
        true
    | VSymbol (Path (_, accs) | Last (_, accs)) ->
        List.exists accs ~f:(function Symbol.Index _ -> true | _ -> false)
    | VSymbol (Abstract _) ->
        true
    | VInjFunction (_, args) ->
        List.exists ~f:is_abstract args
    | VFunction (_, args) ->
        List.exists ~f:is_abstract args
    | VAbsFun (_, _) ->
        true
    | _ ->
        false


  (* check whether a location of a value could points-to everything.
     this function should be used as Loc.is_abstract_heap *)
  let rec __is_abstract_heap = function
    | VAbstract _ ->
        true
    | VSymbol (Abstract _) ->
        true
    | VInjFunction (_, args) ->
        List.exists ~f:__is_abstract_heap args
    | VFunction (_, args) ->
        List.exists ~f:__is_abstract_heap args
    | VAbsFun (_, _) ->
        true
    | _ ->
        false


  let rec is_almost_top_heap = function
    | VAbstract _ ->
        true
    | VInjFunction (_, args) ->
        List.exists ~f:is_almost_top_heap args
    | VFunction (_, args) ->
        List.exists ~f:is_almost_top_heap args
    | VAbsFun (_, _) ->
        true
    | VFreshSymbol (_, _) ->
        true
    | _ ->
        false


  let is_extern = function VInjFunction _ | VFunction _ | VAbsFun _ -> true | _ -> false

  let is_concrete = (* x = y is unSAT if x, y are not equal *)
    function
    | VInt _ | VFloat _ | VString _ | VNull ->
        true
    | VHeap _ ->
        true
    | _ ->
        false


  let is_heap = function VHeap _ -> true | _ -> false

  let is_identifiable_symbol = function VSymbol _ -> true | _ -> false

  let is_symbolic x = not (is_abstract x || is_concrete x)

  let is_global = function VSymbol s -> Symbol.is_global s | _ -> false

  let is_generatable = function
    | VInt _ | VFloat _ | VString _ | VNull | VAbstract _ | VTopPrimitive ->
        false
    | _ ->
        true


  let rec is_strong_updatable ~revisited_allocs = function
    | VHeap n ->
        not (Node.Set.mem n revisited_allocs)
    | VSymbol (Abstract _ | Last _) ->
        false
    | VSymbol _ ->
        true
    | VFreshSymbol _ ->
        true
    | VInjFunction (_, args) | VFunction (_, args) ->
        List.for_all args ~f:(is_strong_updatable ~revisited_allocs)
    | _ ->
        false


  let default_typ_opt = function
    | VInt _ ->
        Some AbsTyp.int
    | VFloat _ | VAbstract AbsFloat ->
        Some AbsTyp.float
    | VString _ | VAbstract AbsString ->
        Some (AbsTyp.make_exact (strip_ptr Typ.pointer_to_java_lang_string))
    | VAbstract AbsHeap ->
        Some AbsTyp.top
    | VNull ->
        Some AbsTyp.null
    | VHeap n ->
        NodeSymbol.get_abstyp_opt n
    | VTopPrimitive ->
        Some AbsTyp.top
    | VAbsFun _ ->
        Some AbsTyp.top
    | VSymbol s ->
        Symbol.default_typ_opt s
    | VFreshSymbol (f, _) | VInjFunction (f, _) | VFunction (f, _) -> (
      match f with
      | Procname.Java mthd ->
          Some (Procname.Java.get_return_typ mthd |> AbsTyp.make_instance)
      | _ -> (
        match Program.pdesc_of_opt (Program.from_marshal ()) f with
        | Some pdesc ->
            Some (Procdesc.get_ret_type pdesc |> AbsTyp.make_instance)
        | None ->
            None ) )


  let is_true = equal one

  let is_false = equal zero

  let is_null = function VNull -> true | _ -> false

  let rec exists ~f = function
    | VInjFunction (_, args) | VFunction (_, args) | VAbsFun (_, args) ->
        List.exists args ~f:(exists ~f)
    | v ->
        f v


  (** Makers **)

  let make_string str = VString str

  let make_int intlit = VInt intlit

  let make_float flit = VFloat (FloatLit.of_float flit)

  let make_hole n = VFreshSymbol (Models.hole, NodeSymbol.make n)

  let make_allocsite n = VHeap (NodeSymbol.make n)

  let make_absfun f args =
    match
      List.find_map args ~f:(function VHeap _ -> None | v when is_abstract v -> Some v | _ -> None)
    with
    | Some v ->
        v
    | None ->
        VAbsFun (f, args)


  let make_uninterpret f args =
    let absval_opt =
      List.find_map args ~f:(function
        | VHeap _ ->
            None
        | VFunction (f', args') | VInjFunction (f', args') ->
            Some (VAbsFun (f', args'))
        | v when is_abstract v ->
            Some v
        | _ ->
            None )
    in
    match absval_opt with Some absval -> absval | None -> VFunction (f, args)


  let make_injective f args =
    let absfun_opt =
      List.find_map args ~f:(function
        | VHeap _ ->
            None
        | VFunction (f', args') | VInjFunction (f', args') ->
            Some (VAbsFun (f', args'))
        | v when is_abstract v ->
            Some v
        | _ ->
            None )
    in
    match absfun_opt with Some v -> v | None -> VInjFunction (f, args)


  let make_commut_inj f v1 v2 =
    (* uninterpret symbol for +, -, * *)
    if is_top_primitive v1 || is_top_primitive v2 then top_primitive
    else
      (* HEURISTICS: sorting for commutative function such as +, * *)
      let sort_for_commutative v1 v2 =
        if is_concrete v1 then [v2; v1]
        else if is_concrete v2 then [v1; v2]
        else List.sort [v1; v2] ~compare
      in
      make_injective f (sort_for_commutative v1 v2)


  let make_fresh_symbol f n = VFreshSymbol (f, NodeSymbol.make n)

  let rec normalize = function
    | VInjFunction (f, [v1; v2]) as v when Procname.equal Models.append f -> (
        let v1' = normalize v1 in
        let v2' = normalize v2 in
        match (v1', v2') with
        | VString str1, VString str2 ->
            String.concat [str1; str2] |> make_string
        | _ ->
            v )
    | VAbstract AbsString ->
        make_string ".*"
    | v ->
        v


  let add v1 v2 =
    if is_symbolic v1 || is_symbolic v2 then make_commut_inj Models.add v1 v2
    else match (v1, v2) with VInt x, VInt y -> VInt (IntLit.add x y) | _ -> top_primitive


  let sub v1 v2 =
    if is_symbolic v1 || is_symbolic v2 then make_injective Models.sub [v1; v2]
    else match (v1, v2) with VInt x, VInt y -> VInt (IntLit.sub x y) | _ -> top_primitive


  let join_float v1 v2 =
    match (v1, v2) with
    | VTopPrimitive, _ | _, VTopPrimitive ->
        top_primitive
    | VFloat FNaN, VFloat FNaN ->
        VFloat FloatLit.nan
    | VFloat FNaN, _ | _, VFloat FNaN ->
        top_primitive
    | VFloat FInf, VFloat FInf ->
        VFloat FloatLit.inf
    | VFloat FInf, _ | _, VFloat FInf ->
        top_primitive
    | VFloat _, VFloat _
    | VFloat _, VAbstract AbsFloat
    | VAbstract AbsFloat, VFloat _
    | VAbstract AbsFloat, VAbstract AbsFloat ->
        VAbstract AbsFloat
    | VFloat _, _ | _, VFloat _ | VAbstract AbsFloat, _ | _, VAbstract AbsFloat ->
        top_primitive
    | _ ->
        top_primitive


  let is_float = function VFloat _ -> true | VAbstract AbsFloat -> true | _ -> false

  let minus_float v =
    match normalize v with
    | VTopPrimitive ->
        top_primitive
    | VFloat FNaN ->
        VFloat FNaN
    | VFloat FInf ->
        VFloat FInf
    | VFloat _ ->
        VAbstract AbsFloat
    | VAbstract AbsFloat ->
        VAbstract AbsFloat
    | _ ->
        top_primitive


  (** For constaint solving *)

  let check_leq x y =
    match (x, y) with
    | VInt x, VInt y ->
        if IntLit.leq x y then Result.Valid else Result.UnSAT
    | _ ->
        Result.Unknown


  let rec check_equal ~get_type ~revisited_allocs ~disjoint_global x y =
    let check_equal = check_equal ~get_type ~revisited_allocs ~disjoint_global in
    let x, y = (normalize x, normalize y) in
    match (x, y) with
    | _ when is_top_primitive x || is_top_primitive y ->
        Result.Satisfiable
    | _ when AbsTyp.is_different (get_type x) (get_type y) ->
        L.d_printfln "check_equal: type mismatch: %a %a" AbsTyp.pp_opt (get_type x) AbsTyp.pp_opt
          (get_type y) ;
        Result.UnSAT
    | VHeap x, VHeap y ->
        if not (NodeSymbol.equal x y) then Result.UnSAT
        else if (not (Node.Set.mem x revisited_allocs)) && not (Node.Set.mem y revisited_allocs)
        then Result.Valid
        else Result.Satisfiable
    | _ when equal x y ->
        if is_abstract x || is_abstract y then Result.Satisfiable else Result.Valid
    | VInt _, VInt _ | VFloat _, VFloat _ ->
        if equal x y then Result.Valid else Result.UnSAT
    | VFloat x, VAbstract AbsFloat | VAbstract AbsFloat, VFloat x ->
        if FloatLit.is_normal x then Result.Satisfiable else Result.UnSAT
    | VString str1, VString str2 -> (
      try
        let regex1 = Str.regexp (String.escaped str1) in
        let regex2 = Str.regexp (String.escaped str2) in
        let is_matched = Str.string_match regex1 str2 0 || Str.string_match regex2 str1 0 in
        (* L.progress "match %s to %s : %b@." str1 str2 is_matched ; *)
        if is_matched then Result.Satisfiable else Result.UnSAT
      with _ -> Result.Satisfiable )
    | VHeap _, VNull | VNull, VHeap _ ->
        Result.UnSAT
    | VInjFunction (f1, [x1]), VInjFunction (f2, [y1]) when Procname.equal f1 f2 ->
        (* x1 = y1 <=> f(x1) = f(y2) *)
        check_equal x1 y1
    | (VInjFunction (f, [x1; x2]), VInt intlit | VInt intlit, VInjFunction (f, [x1; x2]))
      when Procname.equal f Models.sub && IntLit.iszero intlit ->
        (* L.progress "check %a equal to %a@." pp x1 pp x2 ; *)
        check_equal x1 x2
    | VInjFunction (f1, [x1; x2]), VInjFunction (f2, [y1; y2]) when Procname.equal f1 f2 ->
        (* x1 = y1 => [x2 = y2 <=> f(x1)(x2) = f(y1)(y2)]
           OR x2 = y2 => [x1 = y1 <=> f(x1)(x2) = f(y1)(y2)]
           OR x1 = y1 AND x2 = y2 => f(x1)(x2) = f(y1)(y2) *)
        if Result.is_valid (check_equal x1 y1) then check_equal x2 y2
        else if Result.is_valid (check_equal x2 y2) then check_equal x1 y1
        else if
          List.for_all2_exn [x1; x2] [y1; y2] ~f:(fun v1 v2 -> Result.is_valid (check_equal v1 v2))
        then Result.Valid
        else Result.Satisfiable
    | VInjFunction (f1, args1), VInjFunction (f2, args2)
    | VFunction (f1, args1), VFunction (f2, args2)
      when Procname.equal f1 f2 ->
        (* x = y => f(x) = f(y) *)
        if List.for_all2_exn args1 args2 ~f:(fun v1 v2 -> Result.is_valid (check_equal v1 v2)) then
          Result.Valid
        else Result.Satisfiable
    | VFreshSymbol (f1, ext1), VFreshSymbol (f2, ext2) when Procname.equal f1 f2 ->
        if NodeSymbol.equal ext1 ext2 then Result.Valid else Result.UnSAT
    | VSymbol (Path (Global (_, Field fn), [])), VNull
    | VNull, VSymbol (Path (Global (_, Field fn), []))
      when Program.is_nonnull_static_final_field fn ->
        L.d_printfln " - nonnull static field = NULL is UNSAT@." ;
        Result.UnSAT
    | VSymbol (Path (Global _, _)), VSymbol (Path (Global _, _)) when disjoint_global ->
        (* FIXME: this is unsound heuristics *)
        if equal x y then Result.Valid else Result.UnSAT
    | _ ->
        Result.Unknown


  let is_equal_sat ~get_type ~revisited_allocs v1 v2 =
    check_equal ~get_type ~revisited_allocs v1 v2 ~disjoint_global:true |> Result.is_unsat |> not


  let is_equal_valid ~get_type ~revisited_allocs v1 v2 =
    check_equal ~get_type ~revisited_allocs v1 v2 ~disjoint_global:true |> Result.is_valid


  let is_inequal_sat ~get_type ~revisited_allocs v1 v2 =
    check_equal ~get_type ~revisited_allocs v1 v2 ~disjoint_global:true |> Result.is_valid |> not


  let is_inequal_valid ~get_type ~revisited_allocs v1 v2 =
    check_equal ~get_type ~revisited_allocs v1 v2 ~disjoint_global:true |> Result.is_unsat


  let check_equal =
    check_equal ~get_type:default_typ_opt ~revisited_allocs:Node.Set.empty ~disjoint_global:false


  let rec get_subvalues v =
    match v with
    | VInjFunction (_, args) | VFunction (_, args) ->
        v :: List.concat_map args ~f:get_subvalues
    | _ ->
        [v]


  let rec replace_sub (x : t) ~(src : t) ~(dst : t) =
    match (x, dst) with
    | _ when equal x src ->
        dst
    | VInjFunction _, VInjFunction _
    | VInjFunction _, VFunction _
    | VFunction _, VFunction _
    | VFunction _, VInjFunction _ ->
        (* TODO: currently, support only single function *)
        x
    | VInjFunction (mthd, args), _ ->
        let args_replaced = List.map args ~f:(replace_sub ~src ~dst) in
        make_injective mthd args_replaced
    | VFunction (mthd, args), _ ->
        let args_replaced = List.map args ~f:(replace_sub ~src ~dst) in
        make_uninterpret mthd args_replaced
    | _ ->
        (* TODO: support only single function *)
        x


  let rec replace_by_map x ~f =
    match x with
    | VInjFunction (mthd, args) ->
        let args_replaced = List.map args ~f:(replace_by_map ~f) in
        make_injective mthd args_replaced
    | VFunction (mthd, args) ->
        let args_replaced = List.map args ~f:(replace_by_map ~f) in
        make_uninterpret mthd args_replaced
    | VAbsFun (mthd, args) ->
        let args_replaced = List.map args ~f:(replace_by_map ~f) in
        make_absfun mthd args_replaced
    | VSymbol _ ->
        f x
    | _ ->
        x


  let get_default_by_typ typ =
    match Typ.(typ.desc) with
    | Tint _ ->
        zero
    | Tfloat _ ->
        VFloat FloatLit.zero
    | Tptr _ ->
        VNull
    | Tarray {elt} ->
        (* TODO: default value of array *)
        L.d_printfln "   - default value of array ?: %a in %a@." (Typ.pp_full Pp.text) elt
          (Typ.pp_full Pp.text) typ ;
        VNull
    | _ ->
        L.d_printfln "   - default value of %a: typ@." (Typ.pp_full Pp.text) typ ;
        L.progress "[WARNING]: get default by typ %a@." (Typ.pp_full Pp.text) typ ;
        VNull
end

module AbsVal = struct
  include AbstractDomain.FiniteSet (SymVal)

  let top = SymVal.make_absfun Models.hole [] |> singleton

  let top_primitive = singleton SymVal.top_primitive

  let unknown = singleton SymVal.unknown

  let set_add = add

  let zero = singleton SymVal.zero

  let one = singleton SymVal.one

  let add v vals =
    if is_empty vals then singleton v
    else
      match (v, choose vals) with
      | SymVal.VTopPrimitive, x when SymVal.is_primitive x ->
          top_primitive
      | x, SymVal.VTopPrimitive when SymVal.is_primitive x ->
          top_primitive
      | x, _ when SymVal.is_almost_top_heap x ->
          singleton x
      | _, x when SymVal.is_almost_top_heap x ->
          singleton x
      | x, y when SymVal.is_float x && SymVal.is_float y ->
          singleton (SymVal.join_float x y)
      | _ ->
          set_add v vals


  let has_abstract = exists (fun v -> SymVal.is_abstract v || SymVal.is_almost_top_heap v)

  let join x y = if is_empty y then x else if is_empty x then y else fold add x y

  let joinable x y =
    phys_equal x y
    || (has_abstract x && has_abstract y)
    || equal (map SymVal.normalize x) (map SymVal.normalize y)


  let values_list_from_absval_list absval_list =
    List.fold absval_list ~init:[[]] ~f:(fun values_list_acc absval ->
        (* acc = [[v11; v2]; [v12; v2]] + absval = [v31; v32]
           => [[v11; v2; v31]; [v11; v2; v32]; [v12; v2; v31]; [v12; v2; v32] *)
        List.concat_map values_list_acc ~f:(fun values_acc ->
            List.map (elements absval) ~f:(fun value -> values_acc @ [value]) ) )


  let rec replace_symval_by_absval_map (v : SymVal.t) ~f : t =
    match v with
    | SymVal.VFunction (proc, args) ->
        let arglist_list : t list = List.map args ~f:(replace_symval_by_absval_map ~f) in
        let args_list = values_list_from_absval_list arglist_list in
        List.map args_list ~f:(fun args' -> SymVal.make_uninterpret proc args') |> of_list
    | SymVal.VInjFunction (proc, args) ->
        let arglist_list : t list = List.map args ~f:(replace_symval_by_absval_map ~f) in
        let args_list = values_list_from_absval_list arglist_list in
        List.map args_list ~f:(fun args' -> SymVal.make_injective proc args') |> of_list
    | _ ->
        f v


  let get_val_opt (vals : t) = if Int.equal (cardinal vals) 1 then Some (choose vals) else None

  let make_uninterpret f absval_list =
    List.map (values_list_from_absval_list absval_list) ~f:(fun values ->
        SymVal.make_uninterpret f values )
    |> of_list


  let make_injective f absval_list =
    List.map (values_list_from_absval_list absval_list) ~f:(fun values ->
        SymVal.make_injective f values )
    |> of_list


  let make_absfun f absval_list =
    let arg_values = values_list_from_absval_list absval_list in
    if List.is_empty arg_values then top
    else List.map arg_values ~f:(fun values -> SymVal.make_absfun f values) |> of_list


  let replace_sub ~src ~dst = map (SymVal.replace_sub ~src ~dst)

  let replace_by_map ~f = map (SymVal.replace_by_map ~f)

  let is_disjoint lhs rhs =
    for_all (fun v1 -> for_all (fun v2 -> Result.is_unsat (SymVal.check_equal v1 v2)) rhs) lhs


  let get_subvalues t = fold (fun v -> SymVal.get_subvalues v |> of_list |> union) t empty

  let is_singleton_constant t =
    match is_singleton_or_more t with
    | Singleton v ->
        SymVal.is_concrete v && SymVal.is_primitive v
    | _ ->
        false
end

module SymLocCore = struct
  type t =
    | TempVar of Pvar.t
    | Var of Pvar.t
    | SymHeap of SymVal.t
    | Field of t * Fieldname.t
    | Index of t * SymVal.t
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let rec pp fmt = function
    | TempVar v ->
        F.fprintf fmt "(TempPvar) %a" Pvar.pp_value v
    | Var v ->
        F.fprintf fmt "(Pvar) %a" Pvar.pp_value v
    | SymHeap s ->
        F.fprintf fmt "(SymHeap) %a" SymVal.pp s
    | Field ((SymHeap (VSymbol (Last _)) as l), f) ->
        F.fprintf fmt "(Field) (%a)*.(%s)" pp l (Fieldname.to_simplified_string f)
    | Field (l, f) ->
        F.fprintf fmt "(Field) (%a).(%s)" pp l (Fieldname.to_simplified_string f)
    | Index ((SymHeap (VSymbol (Last _)) as l), s) ->
        F.fprintf fmt "(Index) (%a)*[%a]" pp l SymVal.pp s
    | Index (l, s) ->
        F.fprintf fmt "(Index) (%a)[%a]" pp l SymVal.pp s


  let rec is_global = function
    | TempVar _ ->
        false
    | Var v ->
        Pvar.is_global v
    | SymHeap _ ->
        false
    | Field (l, _) ->
        is_global l
    | Index (l, _) ->
        is_global l


  let is_temp = function TempVar _ -> true | _ -> false

  let rec is_heap_pred ~pred = function
    | SymHeap v ->
        pred v
    | Field (l, _) ->
        is_heap_pred ~pred l
    | Index (l, _) ->
        is_heap_pred ~pred l
    | _ ->
        false


  let is_pvar = function TempVar _ | Var _ -> true | _ -> false

  let is_return = function Var pv -> Pvar.is_return pv | _ -> false

  let is_primitive = is_heap_pred ~pred:SymVal.is_primitive

  let is_symbolic = is_heap_pred ~pred:SymVal.is_symbolic

  let is_global = is_heap_pred ~pred:SymVal.is_global

  let is_abstract = is_heap_pred ~pred:SymVal.is_abstract

  let is_invalid = is_heap_pred ~pred:SymVal.is_null

  let is_abstract_heap = function SymHeap v -> SymVal.__is_abstract_heap v | _ -> false

  let is_abstract_symloc = function
    | Field (SymHeap (VSymbol (Last _)), _) | Index (SymHeap (VSymbol (Last _)), _) ->
        true
    | _ ->
        false


  let append_index l ~index:_ =
    match l with
    | SymHeap v when SymVal.is_top_primitive v ->
        l
    | SymHeap (VSymbol (Abstract (base, accs, _))) ->
        let base_loc = SymHeap (VSymbol (Last (base, accs))) in
        Index (base_loc, SymVal.top_primitive)
    | _ when is_abstract_heap l ->
        l
    | _ ->
        Index (l, SymVal.top_primitive)


  let append_field ~fn l =
    match l with
    | SymHeap v when SymVal.is_top_primitive v ->
        (* string could be used as locational value *)
        l
    | SymHeap (VSymbol (Abstract (base, accs, _))) ->
        let base_loc = SymHeap (VSymbol (Last (base, accs))) in
        Field (base_loc, fn)
    | _ when is_abstract_heap l ->
        l
    | _ ->
        Field (l, fn)


  let append_access = function
    | Symbol.Field fn ->
        append_field ~fn
    | Symbol.Index _ ->
        append_index ~index:SymVal.top_primitive


  let of_pvar pv : t = if Pvar.is_frontend_tmp pv then TempVar pv else Var pv

  let of_heap v : t = SymHeap v

  let rec base_of = function Field (l, _) -> base_of l | Index (l, _) -> base_of l | _ as l -> l

  let get_val_opt = function
    | SymHeap v ->
        Some v
    | Field (SymHeap v, _) | Index (SymHeap v, _) ->
        Some v
    | _ ->
        None


  let rec get_vals : t -> SymVal.t list = function
    | TempVar _ | Var _ ->
        []
    | SymHeap v ->
        [v]
    | Field (l, _) ->
        get_vals l
    | Index (l, _) ->
        get_vals l


  let rec replace_heap ~src ~dst = function
    | SymHeap sh when SymVal.equal sh src ->
        SymHeap dst
    | Field (l, fn) ->
        Field (replace_heap l ~src ~dst, fn)
    | Index (l, index) ->
        Index (replace_heap l ~src ~dst, index)
    | _ as l ->
        l


  let to_symbol_opt : t -> Symbol.t option = function
    | Var _ ->
        None
    | Field (Var pv, fn) when Pvar.is_global pv ->
        Some (Symbol.make_global pv fn)
    | Field (SymHeap (VSymbol s), fn) ->
        Some (Symbol.append_field s ~fn)
    | Index (SymHeap (VSymbol s), VTopPrimitive) ->
        (* DECISION: only symbolize a[Top] *)
        Some (Symbol.append_index ~index:IntLit.zero s)
    | _ ->
        None


  let rec is_strong_updatable ~revisited_allocs = function
    | TempVar _ | Var _ ->
        true
    | SymHeap h ->
        SymVal.is_strong_updatable ~revisited_allocs h
    | Field (l, _) ->
        is_strong_updatable ~revisited_allocs l
    | Index (l, i) ->
        is_strong_updatable ~revisited_allocs l && SymVal.is_strong_updatable ~revisited_allocs i


  let rec replace_value ~src ~dst = function
    | SymHeap sheap ->
        SymHeap (SymVal.replace_sub ~src ~dst sheap)
    | Field (l, fn) ->
        Field (replace_value ~src ~dst l, fn)
    | Index (l, v) ->
        Index (replace_value ~src ~dst l, SymVal.replace_sub ~src ~dst v)
    | (TempVar _ | Var _) as l ->
        l


  let rec replace_by_map ~f = function
    | SymHeap v ->
        SymHeap (SymVal.replace_by_map ~f v)
    | Field (l, fn) ->
        Field (replace_by_map ~f l, fn)
    | Index (l, v) ->
        Index (replace_by_map ~f l, SymVal.replace_by_map ~f v)
    | (TempVar _ | Var _) as l ->
        l
end

module SymLoc = struct
  include SymLocCore
  module Set = AbstractDomain.FiniteSet (SymLocCore)

  let from_vals vals = AbsVal.fold (fun v -> Set.add (SymHeap v)) vals Set.empty

  let append_fields ~fn = Set.map (append_field ~fn)

  let append_indexs ?(index = SymVal.top_primitive) = Set.map (append_index ~index)

  let rec replace_loc_by_absval_map ~f =
    let f_sub = AbsVal.replace_symval_by_absval_map ~f in
    function
    | SymHeap sheap ->
        AbsVal.fold (fun v -> Set.add (SymHeap v)) (f_sub sheap) Set.empty
    | Field (l, fn) ->
        replace_loc_by_absval_map l ~f |> append_fields ~fn
    | Index (l, _) ->
        replace_loc_by_absval_map ~f l |> append_indexs
    | (TempVar _ | Var _) as l ->
        Set.singleton l
end

let neg i = if IntLit.iszero i then IntLit.one else IntLit.zero

module PathCond = struct
  include Constraint.Make (SymVal)
end

module PC = struct
  include Constraint.MakePC (SymVal)
end

module Reg = struct
  include WeakMap.Make (Ident) (AbsVal)

  let equal f x y = phys_equal x y || equal f x y
end

module Mem = struct
  (* Allocsite[Index] has null as default value 
   * Other location has bottom as default value *)
  include WeakMap.Make (SymLoc) (AbsVal)

  let add l v t = if SymLoc.is_primitive l then t else add l v t

  let weak_update l v t = if SymLoc.is_primitive l then t else weak_update l v t

  let strong_update l v t = if SymLoc.is_primitive l then t else strong_update l v t

  let update ~is_weak = if is_weak then weak_update else strong_update

  let equal lhs rhs = if phys_equal lhs rhs then true else equal AbsVal.joinable lhs rhs

  let joinable lhs rhs =
    let locs_lhs = fold (fun l _ -> SymLoc.Set.add l) lhs SymLoc.Set.empty in
    let locs_rhs = fold (fun l _ -> SymLoc.Set.add l) rhs SymLoc.Set.empty in
    let locs = SymLoc.Set.inter locs_lhs locs_rhs in
    SymLoc.Set.for_all (fun l -> AbsVal.joinable (find l lhs) (find l rhs)) locs


  let replace_value ~src ~dst t =
    fold
      (fun l v -> weak_update (SymLoc.replace_value ~src ~dst l) (AbsVal.replace_sub ~src ~dst v))
      t empty


  let replace_by_map ~f t =
    fold (fun l v -> weak_update (SymLoc.replace_by_map ~f l) (AbsVal.replace_by_map ~f v)) t empty


  let filter_by_value ~f t =
    fold
      (fun l vals acc ->
        if List.for_all (SymLoc.get_vals l) ~f then strong_update l (AbsVal.filter f vals) acc
        else acc )
      t empty
end

module VTMap = struct
  include WeakMap.Make (SymVal) (AbsTyp)

  let weak_update v abstyp t =
    if SymVal.is_null v then t
    else if SymVal.is_top_primitive v then t
    else if SymVal.is_abstract v then t
    else
      match (find_opt v t, SymVal.default_typ_opt v) with
      | Some abstyp_old, _ when AbsTyp.leq ~lhs:abstyp ~rhs:abstyp_old ->
          (* skip weak-update when updating to specific type *)
          t
      | Some _, Some default_typ when AbsTyp.leq ~lhs:default_typ ~rhs:abstyp ->
          remove v t
      | None, Some default_typ when AbsTyp.leq ~lhs:default_typ ~rhs:abstyp ->
          t
      | _, Some default_typ when AbsTyp.leq ~lhs:abstyp ~rhs:default_typ ->
          strong_update v abstyp t
      | Some _, Some _ ->
          (* invalid type given, use default type *)
          remove v t
      | None, Some _ ->
          (* invalid type given, use default type *)
          t
      | _, None ->
          weak_update v abstyp t


  let find_opt v t =
    let v = SymVal.normalize v in
    match find_opt v t with Some abstyp -> Some abstyp | None -> SymVal.default_typ_opt v


  let strong_update v abstyp t =
    if SymVal.is_null v then t
    else if SymVal.is_top_primitive v then t
    else if SymVal.is_abstract v then t
    else
      match find_opt v t with
      | Some (Exact _) ->
          t
      | Some abstyp_old when AbsTyp.leq ~lhs:abstyp_old ~rhs:abstyp ->
          (* skip strong-update when updating to general type *)
          t
      | Some abstyp_old when AbsTyp.is_different (Some abstyp) (Some abstyp_old) ->
          L.d_printfln "type %a and %a are different, so invalidate type of %a" AbsTyp.pp abstyp
            AbsTyp.pp abstyp_old SymVal.pp v ;
          strong_update v AbsTyp.invalid t
      | org ->
          L.d_printfln "update %a to %a" (Pp.option AbsTyp.pp) org AbsTyp.pp abstyp ;
          strong_update v abstyp t


  let update ~is_weak = if is_weak then weak_update else strong_update

  let find v t =
    match find_opt v t with
    | Some abstyp ->
        abstyp
    | None ->
        (* raise (Unexpected (F.asprintf "%a's type is undefined" SymVal.pp v)) *)
        AbsTyp.top


  let find_vals vals t =
    AbsVal.fold
      (fun v ->
        (* FIXME: no opt here *)
        match find_opt v t with Some abstyp -> AbsTyp.join abstyp | None -> AbsTyp.join AbsTyp.top
        )
      vals AbsTyp.bottom


  let leq ~lhs ~rhs =
    if phys_equal lhs rhs then true
    else
      for_all
        (fun k lhs_v -> if mem k rhs then AbsTyp.leq ~lhs:lhs_v ~rhs:(find k rhs) else true)
        lhs


  let leq ~lhs ~rhs =
    let result = leq ~lhs ~rhs in
    result


  let collect_important_values t =
    let fields_to_distinguish = Program.collect_callback_fields (Program.from_marshal ()) in
    fold
      (fun v _ acc ->
        let is_important_val =
          match v with
          | SymVal.VSymbol (Path (Param (_, pv), accesses)) -> (
            match List.rev accesses with
            | Field fn :: _ when List.mem ~equal:Fieldname.equal fields_to_distinguish fn ->
                true
            | [] when String.is_suffix ~suffix:"cb" (Pvar.to_string pv) ->
                true
            | _ ->
                false )
          | _ ->
              false
        in
        if is_important_val then AbsVal.set_add v acc else acc )
      t AbsVal.empty


  let joinable ~lhs ~rhs =
    let lhs_vals, rhs_vals = (collect_important_values lhs, collect_important_values rhs) in
    AbsVal.for_all
      (fun v ->
        match (mem v lhs, mem v rhs) with
        | true, true ->
            not (AbsTyp.is_different (find_opt v lhs) (find_opt v rhs))
        | true, false | false, true ->
            (* to prevent join with empty state *)
            false
        | false, false ->
            true )
      (AbsVal.union lhs_vals rhs_vals)


  let join ~lhs ~rhs =
    if phys_equal lhs rhs then lhs
    else
      merge
        (fun v t1_opt t2_opt ->
          match (t1_opt, t2_opt) with
          | Some t1, Some t2 ->
              Some (AbsTyp.join t1 t2)
          | Some t1, None -> (
            match (find_opt v rhs, SymVal.default_typ_opt v) with
            | Some t2, Some t_default ->
                let t_joined = AbsTyp.join t1 t2 in
                if AbsTyp.equal t_joined t_default then None else Some (AbsTyp.join t1 t2)
            | Some t2, None ->
                Some (AbsTyp.join t1 t2)
            | None, _ ->
                Some t1 )
          | None, Some t2 -> (
            match find_opt v lhs with Some t1 -> Some (AbsTyp.join t1 t2) | None -> Some t2 )
          | None, None ->
              None )
        lhs rhs
end

module AssertCond = struct
  type t = AbsVal.t * AbsVal.t * Binop.t * InstrNode.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt (v1, v2, kind, node) =
    F.fprintf fmt "%a %s %a (%a)" AbsVal.pp v1 (Binop.str Pp.text kind) AbsVal.pp v2 InstrNode.pp
      node


  let is_sat ~get_type ~revisited_allocs (vals1, vals2, kind, _) =
    match kind with
    | Binop.Eq ->
        AbsVal.exists
          (fun v1 -> AbsVal.exists (SymVal.is_equal_sat ~get_type ~revisited_allocs v1) vals2)
          vals1
    | Binop.Ne ->
        AbsVal.exists
          (fun v1 -> AbsVal.exists (SymVal.is_inequal_sat ~get_type ~revisited_allocs v1) vals2)
          vals1
    | _ ->
        true
end

module ReplacedValMap = struct
  include PrettyPrintable.MakePPMonoMap (SymVal) (SymVal)

  (* TODO: design sound join *)

  let join lhs rhs =
    merge
      (fun _ v1_opt v2_opt ->
        (* replace from symbolic to concrete : should be intersected *)
        match (v1_opt, v2_opt) with
        | Some v1, Some v2 when SymVal.equal v1 v2 ->
            Some v1
        | _ ->
            None )
      lhs rhs
end
