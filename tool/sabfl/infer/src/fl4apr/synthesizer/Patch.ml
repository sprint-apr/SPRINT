open! IStd
open! Vocab
module F = Format
module AE = ASTExp

module Kind = struct
  type t =
    | ExpReplacement of {e_org: Exp.t; e_rep: AE.t; ty_org: Typ.t}
    | MutateCastingType of {e_match: Exp.t; ty_org: Typ.t; ty_to: Typ.t}
    | MutateVarDeclType of {pvar: Pvar.t; ty_from: Typ.t; ty_to: Typ.t; decl_loc: Location.t}
    | InsertHandle of {cond: AE.t; hkind: hkind}
    | InsertMethodCall of {method_call: AE.t}
    | SkipStmt of {cond: AE.t; is_continue: bool}
    | ReplaceLine
    | InsertLine

  and hkind = Return of AE.t option | Throw of AE.t [@@deriving compare]

  let pp fmt = function
    | ExpReplacement {e_org; e_rep; ty_org} ->
        F.fprintf fmt "ExpReplacement(%a, %a, %s)" Exp.pp e_org AE.pp e_rep (Typ.to_string ty_org)
    | MutateCastingType {e_match; ty_org} ->
        F.fprintf fmt "MutateCastingType(%a, %s)" Exp.pp e_match (Typ.to_string ty_org)
    | MutateVarDeclType {pvar; ty_from; ty_to} ->
        F.fprintf fmt "MutateVarDeclType((%a -> %a), %a)" (Typ.pp_full Pp.text) ty_from
          (Typ.pp_full Pp.text) ty_to Pvar.pp_value pvar
    | InsertHandle {cond; hkind= Return ret_exp_opt} ->
        let return_exp_str = Option.value_map ~default:"" ~f:AE.to_string ret_exp_opt in
        F.fprintf fmt "if (%a) return %s;" AE.pp cond return_exp_str
    | InsertHandle {cond; hkind= Throw throw_exp} ->
        F.fprintf fmt "if (%a) throw %a;" AE.pp cond AE.pp throw_exp
    | InsertMethodCall {method_call} ->
        F.fprintf fmt "InsertCall %a;" ASTExp.pp method_call
    | SkipStmt {cond; is_continue} ->
        F.fprintf fmt "if (%a) %s" AE.pp cond (if is_continue then "continue;" else "")
    | ReplaceLine ->
        F.fprintf fmt "+- %a" AE.pp (AE.Hole Typ.void_star)
    | InsertLine ->
        F.fprintf fmt "+ %a" AE.pp (AE.Hole Typ.void_star)


  type jsonable = {name: name; contents: string} [@@deriving to_yojson]

  and name =
    [ `ExpReplacement
    | `MutateCastingType
    | `MutateVarDeclType
    | `InsertHandle
    | `InsertMethodCall
    | `SkipStmt
    | `ReplaceLine
    | `InsertLine ]

  let jsonable_from_kind k =
    let name =
      match k with
      | ExpReplacement _ ->
          `ExpReplacement
      | MutateCastingType _ ->
          `MutateCastingType
      | MutateVarDeclType _ ->
          `MutateVarDeclType
      | InsertHandle _ ->
          `InsertHandle
      | InsertMethodCall _ ->
          `InsertMethodCall
      | SkipStmt _ ->
          `SkipStmt
      | ReplaceLine ->
          `ReplaceLine
      | InsertLine ->
          `InsertLine
    in
    {name; contents= F.asprintf "%a" pp k}


  let to_yojson = jsonable_from_kind >>> jsonable_to_yojson
end

let procname_to_yojson procname = `String (Procname.to_simplified_string procname)

let location_to_yojson =
  Fault.get_location_node >>> InstrNode.inode_of >>> InterNode.get_int_id >>> fun id -> `Int id


let source_location_to_yojson Location.{file; line} =
  `Assoc [("file", `String (SourceFile.to_rel_path file)); ("line", `Int line)]


type t =
  { id: int [@compare.ignore]
  ; kind: Kind.t
  ; procname: Procname.t [@to_yojson procname_to_yojson]
  ; location: Fault.location [@to_yojson location_to_yojson]
  ; source_location: Location.t [@to_yojson source_location_to_yojson] }
[@@deriving compare, to_yojson]

let pp fmt {id; kind} = F.fprintf fmt "[%d] %a" id Kind.pp kind

let id = ref 0

let mk ~location ~kind =
  incr id ;
  let faulty_node = Fault.get_location_node location in
  match kind with
  | Kind.MutateVarDeclType {decl_loc} ->
      { id= !id
      ; kind
      ; procname= Fault.Node.get_proc_name faulty_node
      ; location
      ; source_location= decl_loc }
  | _ ->
      { id= !id
      ; kind
      ; procname= Fault.Node.get_proc_name faulty_node
      ; location
      ; source_location= Fault.Node.get_loc faulty_node }


let get_expressions {kind} =
  match kind with
  | ExpReplacement {e_rep} ->
      [e_rep]
  | MutateCastingType _ ->
      []
  | InsertHandle {cond; hkind= Return (Some ret)} ->
      [cond; ret]
  | InsertHandle {cond; hkind= Return None} ->
      [cond]
  | InsertHandle {cond; hkind= Throw _} ->
      [cond]
  | SkipStmt {cond} ->
      [cond]
  | InsertMethodCall {method_call} ->
      [method_call]
  | MutateVarDeclType _ ->
      []
  | ReplaceLine ->
      []
  | InsertLine ->
      []


module Set = PrettyPrintable.MakePPSet (struct
  type nonrec t = t

  let compare = compare

  let pp = pp
end)
