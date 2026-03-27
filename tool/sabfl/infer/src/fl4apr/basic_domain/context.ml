open! IStd
open! Vocab
module F = Format
module Node = InstrNode

module type S = sig
  type t = Node.t list

  val empty : t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val of_callsite : Node.t -> t

  val merge : t -> t -> t

  val append : t -> Node.t -> t

  val pop : t -> t

  val mem : t -> Node.t -> bool

  val pp : F.formatter -> t -> unit
end

module Base = struct
  type t = Node.t list [@@deriving compare]

  let empty = []

  let equal = [%compare.equal: t]

  let of_callsite n = [n]

  let mem = List.mem ~equal:Node.equal

  let pp fmt x = match x with [] -> F.fprintf fmt "\"\"" | _ -> (Pp.seq Node.pp_pretty) fmt x
end

module EmptyCtx = struct
  include Base

  let of_callsite _ = []

  let merge _ _ = []

  let append _ _ = []

  let pop _ = []
end

module KLimited (K : sig
  val k : int
end) =
struct
  include Base

  let k = K.k

  let _ = assert (k >= 0)

  let remove_first = function [] -> [] | _ :: tl -> tl

  let append (acc : t) (c : Node.t) : t =
    if mem acc c then (* recursive case *)
      acc
    else if List.length acc >= k then (* k-limited *)
      remove_first acc @ [c]
    else acc @ [c]


  let merge acc c = if List.length acc >= k then remove_first acc @ c else acc @ c

  let pop = remove_first

  let is_empty = function [] -> true | _ -> false

  let dummy : t = [Node.dummy]

  let empty = []

  let is_dummy = function [x] -> Node.equal Node.dummy x | _ -> false

  module Set = PrettyPrintable.MakePPSet (Base)
  module Map = PrettyPrintable.MakePPMap (Base)
end

module TestContext = struct
  type t = Test of Typ.Name.t * Node.t | Dummy | Empty of Typ.Name.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let empty ~testClass = Empty testClass

  let dummy = Dummy

  let of_callsite ~testClass node = Test (testClass, node)

  let is_dummy = equal dummy

  let is_empty = function Empty _ -> true | _ -> false

  let pp fmt = function
    | Test (testClass, node) ->
        F.fprintf fmt "(%s, %a)"
          (String.rsplit2_exn ~on:'.' (Typ.Name.name testClass) |> snd)
          Node.pp_pretty node
    | Empty testClass ->
        F.fprintf fmt "Empty (%s)" (String.rsplit2_exn ~on:'.' (Typ.Name.name testClass) |> snd)
    | Dummy ->
        F.fprintf fmt "Dummy"
end
