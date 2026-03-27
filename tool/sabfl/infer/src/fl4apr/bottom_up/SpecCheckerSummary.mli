open! IStd
module Domain = SpecCheckerDomain

type t

type analysis_data = Procname.t -> t option

type get_summary = Procname.t -> t option

val pp : Format.formatter -> t -> unit

val empty : t

val to_summary : Procdesc.t -> Domain.t list -> t

val get_disjuncts : t -> Domain.t list

val get_local_disjuncts : t -> Domain.t list

val get_only_normals : t -> t

val instantiate_summary :
     Program.t
  -> Domain.t
  -> analysis_data
  -> Procdesc.Node.t
  -> Sil.instr
  -> Ident.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> Procname.t
  -> Domain.t list option

val init : Procdesc.t -> Domain.t list
