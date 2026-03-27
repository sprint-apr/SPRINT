type t = (float * Location.t) list

val parse : Program.t -> t

val parse_bug_positions : Program.t -> t

val pp : Formatter.t -> t -> unit
