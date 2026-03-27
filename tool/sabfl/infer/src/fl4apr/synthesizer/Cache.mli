open! IStd

type ('a, 'b) t

val create : unit -> ('a, 'b) t

val find_or_compute : ('a, 'b) t -> 'a -> compute:(unit -> 'b) -> 'b
