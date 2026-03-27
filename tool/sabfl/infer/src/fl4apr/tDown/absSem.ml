open! IStd
module F = Format

module type S = sig
  module Domain : sig
    include AbstractDomain.WithBottom

    val compare : t -> t -> int
  end

  type analysis_data

  val exec_instr : analysis_data -> Program.t -> InstrNode.t -> Sil.instr -> Domain.t -> Domain.t

  val bind_arguments :
       analysis_data
    -> Program.t
    -> InstrNode.t
    -> Procname.t
    -> Sil.instr
    -> (Pvar.t * Typ.t) list
    -> (Exp.t * Typ.t) list
    -> Domain.t
    -> Domain.t

  val bind_retvar :
       analysis_data
    -> Program.t
    -> InstrNode.t
    -> Sil.instr
    -> Procname.t
    -> Ident.t * Typ.t
    -> Pvar.t
    -> Domain.t
    -> Domain.t

  val handling_undefined :
       analysis_data
    -> Program.t
    -> InstrNode.t
    -> Procname.t
    -> (Exp.t * Typ.t) list
    -> Ident.t * Typ.t
    -> Domain.t
    -> Domain.t

  val is_exceptional : Domain.t -> bool

  val initial_state : Domain.t

  val pp_session_name : InstrNode.t -> F.formatter -> unit
end
