open! IStd
open! Vocab
module F = Format
module L = Logging
module Domain = SpecCheckerDomain
module Symbol = SymDom.Symbol
module Loc = SymDom.SymLoc
module Val = SymDom.SymVal
module AbsVal = SymDom.AbsVal
module DiffVal = Domain.DiffVal
module Disjunct = Domain.Disjunct
module SymDiff = Domain.SymDiff

let filter_trivial_diff mthd astate =
  let has_modify_fn fn = function
    | Fault.{desc= MissingSideEffect (_, fn')} ->
        Fieldname.equal fn fn'
    | _ ->
        false
  in
  match (Domain.(astate.abs_patches), Procname.Java.get_access mthd) with
  (* HEURISTICS: erase unwanted side-effect *)
  | Some abs_patches, Procname.Java.Access.Public when not (Procname.Java.is_constructor mthd) ->
      let mem =
        Domain.Mem.filter
          (fun l v ->
            match (l, AbsVal.is_singleton_or_more v) with
            | Loc.Field (SymHeap (VSymbol _), fn), Singleton (Val.VFreshSymbol _) ->
                not (Fault.Set.exists (has_modify_fn fn) abs_patches)
            | _ ->
                true )
          Domain.(astate.mem)
      in
      if Domain.Mem.is_bottom mem then None else Some Domain.{astate with mem}
  | _ ->
      Some astate


let simplify_summaries proc_desc disjuncts =
  let is_boolean_is proc_desc =
    let proc = Procdesc.get_proc_name proc_desc in
    let ret_var = Procdesc.get_ret_var proc_desc in
    let mthd_name = Procname.get_method proc in
    if String.is_prefix ~prefix:"is" mthd_name then
      match Procdesc.get_ret_type proc_desc with Typ.{desc= Tint IBool} -> true | _ -> false
    else if String.is_prefix ~prefix:"get" mthd_name then
      let is_getter astate =
        match Domain.read_loc_opt astate (Domain.Loc.of_pvar ret_var) with
        | Some vals when AbsVal.has_abstract vals ->
            true
        | Some vals ->
            AbsVal.exists
              (function VSymbol s -> not (Symbol.endswith mValuesField s) | _ -> false)
              vals
        | None ->
            false
      in
      List.filter disjuncts ~f:Domain.is_original |> List.exists ~f:is_getter
    else false
  in
  List.map disjuncts ~f:(fun astate ->
      if Domain.is_exceptional astate || is_boolean_is proc_desc then
        let ret_loc = Procdesc.get_ret_var proc_desc |> Loc.of_pvar in
        let base_locs = Loc.Set.singleton ret_loc in
        let base_vals = Domain.(astate.important_param) in
        let reachable_locs, reachable_vals =
          Domain.compute_reachability_from_base astate ~base_locs ~base_vals
        in
        (* FIXME: unsound heuristics *)
        let mem =
          Domain.(
            Mem.filter
              (fun l _ ->
                match Loc.to_symbol_opt l with Some s -> not (Symbol.is_this s) | _ -> true )
              astate.mem )
        in
        Domain.remove_unreachables Domain.{astate with mem} ~reachable_locs ~reachable_vals
      else astate )
