open! IStd
module Node = InstrNode

type result = SAT | UnSAT | NoChange | ExnSAT | ExnUnSAT | Unexecuted | Unsound

type status = Feasible | NoExnSat | Unreachable | ExistExnSat | Infeasible

type t =
  { id: int
  ; desc: description
  ; loc: location
  ; org_instr: Sil.instr
  ; new_instrs: Sil.instr list
  ; score: float
  ; mutable results: result Array.t
  ; mutable status: status
  ; mutable is_redundant: bool }

and description =
  | WrongExp of (Exp.t * Typ.t)
  | MissingSideEffect of Pvar.t * Fieldname.t
  | MissingErrorHandling of [`Return | `Throw of Typ.t]
  | ShouldSkip

and location = Inplace of Node.t | Before of Node.t | After of Node.t | Range of location * location
[@@deriving compare]

val compare : t -> t -> int

val equal : t -> t -> bool

val is_hole : Exp.t -> bool

val description_name : t -> string

val get_location_node : location -> Node.t

val get_line_file : t -> int * string

val get_proc_name : t -> Procname.t

val pp : Format.formatter -> t -> unit

val pp_full : Format.formatter -> t -> unit

val pp_results : Format.formatter -> t -> unit

val pp_list : ?with_sort:bool -> Format.formatter -> t list -> unit

val equal : t -> t -> bool

val marshal_path : string

val to_marshal : ?path:string -> t list -> unit

val from_marshal : ?path:string -> unit -> t list

val enumerate : float * Location.t -> t list

val id_of : t -> string

val exists_exn_sat : t -> bool

val set_redundant : t -> unit

module Set : PrettyPrintable.PPSet with type elt = t

module Map : PrettyPrintable.PPMap with type key = t
