open! IStd

type package = string

type klass = Typ.Name.t

module type S = sig
  type component

  type on

  val collect : ?pred:(component -> bool) -> on -> component list
end

module Variables : S with type component = Pvar.t * Typ.t and type on = Procname.t

module Literals : S with type component = Const.t and type on = package

module Classes : S with type component = Typ.Name.t and type on = package

module Methods : S with type component = Procname.Java.t and type on = klass

module Fields : S with type component = Fieldname.t and type on = klass

module AccessExpressions : S with type component = ASTExp.t and type on = Procname.t
