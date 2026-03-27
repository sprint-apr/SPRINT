open! IStd

val enum_expressions :
  ?terminals_only:bool -> ?initial_expression:ASTExp.t -> max_cost:int -> Procname.t -> ASTExp.t list

val enum_default : Typ.t -> ASTExp.t
