module Domain = SpecCheckerDomain
module DiffVal = Domain.DiffVal
module SymDiff = Domain.SymDiff
module Loc = Domain.Loc

type exec =
     Domain.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> instantiate:(Domain.t -> Ident.t * Typ.t -> (Exp.t * Typ.t) list -> Procname.t -> Domain.t list option)
  -> callee:Procname.t
  -> (Exp.t * Typ.t) list
  -> (DiffVal.t * Domain.t) list

val dispatch : Procname.t -> Typ.t list -> exec option

module Collection : sig
  val setIsEmpty : Procdesc.Node.t -> Sil.instr -> Domain.Loc.Set.t * SymDiff.t -> Domain.t -> Domain.t
end
