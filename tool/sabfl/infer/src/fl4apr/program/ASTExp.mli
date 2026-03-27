open! IStd
module Method = Procname.Java

type 'a hole = Empty of Typ.t | Filled of 'a

val pp_hole : Format.formatter -> pp_value:(Format.formatter -> 'a -> unit) -> 'a hole -> unit

module Literal : sig
  type t =
    | Integer of IntLit.t
    | NULL
    | Boolean of bool
    | Float of float
    | String of string
    | Class of Ident.name

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val of_const : Const.t -> t

  val pp : Format.formatter -> t -> unit

  val null : t

  val typeof : t -> Typ.t
end

module Ty : sig
  val null : Typ.t

  val any_type : Typ.t

  val any_primitive_type : Typ.t

  val is_subtype_of : Typ.t -> Typ.t -> Vocab.three_value

  val maybe_subtype_of : Typ.t -> Typ.t -> bool

  val get_return_type : Procname.Java.t -> Typ.t
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

and base = StaticAccess of Typ.name hole | DynamicAccess of t

val pp : Format.formatter -> t -> unit

val pp_base : Format.formatter -> base -> unit

val to_string : t -> string

val to_yojson : t -> Yojson.t

val equal : t -> t -> bool

val mask_token : t

val null : t

val lit_true : t

val lit_false : t

val default_of : Typ.t -> t list

val instanceof : Method.t

val of_var : Pvar.t * Typ.t -> t

val of_const : Const.t -> t

val from_IR_exp : Procdesc.t -> Exp.t -> t

val from_IR_exp_opt : Procdesc.t -> Exp.t -> t option

val mk_this : Procname.t -> t

val is_this : t -> bool

val object_hole : t

val any_type_hole : t

val any_primitive_type_hole : t

val any_type_component_hole : 'a hole

val any_primitive_type_component_hole : 'a hole

val typeof : t -> Typ.t

val get_base_exn : t -> base

val get_class_of_base : base -> Typ.name option

val is_static : base -> bool

val maybe_subtype_of : t -> ty:Typ.t -> bool

val is_null : t -> bool

val is_zero : t -> bool

val is_terminal : t -> bool

val is_base_terminal : base -> bool

val is_constant : t -> bool

val number_of_holes : t -> int

module Accessibility : sig
  val is_accessible_method : from:Typ.name -> Method.t -> bool

  val is_accessible_field : from:Typ.name -> Fieldname.t -> bool

  val is_accessible_method : base:base -> from:Typ.name -> Method.t -> bool

  val is_accessible_field : base:base -> from:Typ.name -> Fieldname.t -> bool
end

module Set : Caml.Set.S with type elt = t

val typeof_exp_opt : Procdesc.t -> Exp.t -> Typ.t option
