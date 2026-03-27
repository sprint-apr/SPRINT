open! IStd
open! Vocab
module F = Format
module L = Logging
module Node = InstrNode
module Loc = SymDom.SymLoc
module Val = SymDom.SymVal
module AbsVal = SymDom.AbsVal
module AbsTyp = SymDom.AbsTyp
module PathCond = SymDom.PathCond
module PC = SymDom.PC
module Symbol = SymDom.Symbol
module Models = BasicDom.Models
module Reg = SymDom.Reg
module Mem = SymDom.Mem
module Context = SymDom.Context
module Contexts = SymDom.Contexts
module VTMap = SymDom.VTMap
module Vars = PrettyPrintable.MakePPSet (Var)
module Fault = Fault
module AssertCond = SymDom.AssertCond
module AssertConds = AbstractDomain.FiniteSet (AssertCond)
module ReplacedValMap = SymDom.ReplacedValMap

module Disjunct = struct
  include AbstractDomain.FiniteSet (Symbol)

  let singleton x = add x empty

  let of_values values =
    AbsVal.fold
      (fun v acc ->
        match v with
        | Val.VSymbol s when Symbol.is_global s ->
            acc
        | Val.VSymbol s ->
            add s acc
        | _ ->
            acc )
      values empty


  let of_symbols symbols = List.fold symbols ~init:empty ~f:(fun acc s -> add s acc)

  let to_vals t = fold (fun s -> AbsVal.set_add (Val.VSymbol s)) t AbsVal.empty
end

module IdUse = WeakMap.Make (Ident) (Disjunct)

module LocUse = struct
  include WeakMap.Make (Loc) (Disjunct)

  let trivial_uses l =
    match Loc.to_symbol_opt l with
    | Some s when Symbol.is_global s ->
        Disjunct.empty
    | Some s ->
        (* FIXME: *)
        Disjunct.singleton s
    | _ ->
        Disjunct.empty


  let filter_nontrivial_uses l d =
    Disjunct.filter (fun s -> not (Disjunct.mem s (trivial_uses l))) d


  let find l t = Disjunct.union (find l t) (trivial_uses l)

  let update ~is_weak l d t =
    let d = filter_nontrivial_uses l d in
    if Disjunct.is_empty d then t else update ~is_weak l d t
end

module LocDef = struct
  include WeakMap.Make (Loc) (Node.ASet)
end

module SymDiff = struct
  type t = Org of Disjunct.t | Diff [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt = function
    | Diff ->
        F.fprintf fmt "Diff"
    | Org uses ->
        F.fprintf fmt "Org(%a)" Disjunct.pp uses


  let join x y =
    match (x, y) with
    | Diff, _ | _, Diff ->
        Diff
    | Org x_uses, Org y_uses ->
        Org (Disjunct.join x_uses y_uses)


  let of_uses uses = Org uses

  let uses_of = function Org uses -> uses | Diff -> Disjunct.empty

  let is_diff = function Diff -> true | _ -> false

  let diff = Diff

  let empty = Org Disjunct.empty

  let is_empty = equal empty
end

module DiffVal = struct
  type t = AbsVal.t * SymDiff.t [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt (v, symdiff) = F.fprintf fmt "%a (%a)" AbsVal.pp v SymDiff.pp symdiff

  let join (lhs_v, lhs_symdiff) (rhs_v, rhs_symdiff) =
    (AbsVal.join lhs_v rhs_v, SymDiff.join lhs_symdiff rhs_symdiff)


  let union (lhs_v, lhs_symdiff) (rhs_v, rhs_symdiff) =
    (AbsVal.union lhs_v rhs_v, SymDiff.join lhs_symdiff rhs_symdiff)


  let empty = (AbsVal.empty, SymDiff.empty)

  let top = (Val.make_absfun Models.hole [] |> AbsVal.singleton, SymDiff.diff)

  let is_difftop (v, diff) = SymDiff.is_diff diff && AbsVal.exists Val.is_abstract v
end

module Changed = struct
  include Disjunct

  let from_values values =
    AbsVal.fold
      (function VSymbol s when not (Symbol.is_global s) -> add s | _ -> fun x -> x)
      values empty


  let add_disjunct t x = if is_empty t then x else t

  let join = union

  let is_changed ~is_symbol_changed t : bool =
    if is_empty t then true else exists is_symbol_changed t


  let is_changable ~f t : bool =
    if is_empty t then true
    else
      exists
        (fun s ->
          let values, symdiff = f s in
          match symdiff with
          | SymDiff.Diff ->
              true
          | SymDiff.Org _ ->
              (* TODO: uses or values? *)
              not (is_empty (from_values values)) )
        t


  let get_values t = elements t |> List.map ~f:(fun s -> Val.VSymbol s) |> AbsVal.of_list

  let replace_if_unchanged ~f t =
    if for_all (fun s -> match f s with _, SymDiff.Org _ -> true | _ -> false) t then
      fold
        (fun s acc ->
          let values, symdiff = f s in
          match (symdiff, s) with
          | SymDiff.Diff, _ ->
              acc
          (* FIXME: is this required?
             | SymDiff.Org uses, Symbol.Abstract _ ->
                 union uses acc *)
          | SymDiff.Org _, _ ->
              (* TODO: uses or values? *)
              union (from_values values) acc )
        t empty
    else empty


  let update_by_callee = union
end

module AbsFault = struct
  type t = Fault.Set.t option [@@deriving compare]

  let equal = [%compare.equal: t]

  let pp fmt : t -> unit = function
    | None ->
        F.fprintf fmt "NoFault"
    | Some abs_patches ->
        Fault.Set.pp fmt abs_patches


  let equal x y = if phys_equal x y then true else equal x y

  let join x y : t =
    match (x, y) with
    | _ when phys_equal x y ->
        x
    | Some x, Some y ->
        Some (Fault.Set.union x y)
    | Some _, None ->
        x
    | None, Some _ ->
        y
    | None, None ->
        None


  let is_original = function Some _ -> false | None -> true
end

module ControlDeps = struct
  module Key = struct
    type t = Exp.t * Procdesc.Node.t option [@@deriving compare]

    let pp fmt (e, node_opt) =
      match node_opt with
      | Some node ->
          F.fprintf fmt "Call %a at %a" Exp.pp e Procdesc.Node.pp node
      | None ->
          F.fprintf fmt "Prune %a" Exp.pp e
  end

  include WeakMap.Make (Key) (AbsBool)

  let is_covered diff ~org =
    for_all (fun k v_diff -> AbsBool.leq ~lhs:v_diff ~rhs:(find k org)) diff
    && for_all
         (fun k v_org ->
           if AbsBool.is_top v_org then true
           else
             let lhs = match find k diff with AbsBool.Bot -> AbsBool.Top | v -> v in
             AbsBool.leq ~lhs ~rhs:v_org )
         org


  let find node t =
    match InstrNode.get_instr node with
    | Sil.Prune (UnOp (Unop.LNot, e, _), _, _, _) ->
        find (e, None) t |> AbsBool.negate
    | Sil.Prune (e, _, _, _) ->
        find (e, None) t
    | Sil.Call (_, fexp, _, _, _) ->
        find (fexp, Some (InstrNode.pnode_of node)) t
    | Sil.Load {e} ->
        find (e, Some (InstrNode.pnode_of node)) t
    | Sil.Store {e1} ->
        find (e1, Some (InstrNode.pnode_of node)) t
    | _ ->
        AbsBool.bottom


  let update node v t =
    match InstrNode.get_instr node with
    | Sil.Prune (UnOp (Unop.LNot, e, _), _, _, _) ->
        weak_update (e, None) (AbsBool.negate v) t
    | Sil.Prune (e, _, _, _) ->
        weak_update (e, None) v t
    | Sil.Call (_, fexp, _, _, _) ->
        strong_update (fexp, Some (InstrNode.pnode_of node)) v t
    | Sil.Load {e} ->
        strong_update (e, Some (InstrNode.pnode_of node)) v t
    | Sil.Store {e1} ->
        strong_update (e1, Some (InstrNode.pnode_of node)) v t
    | _ ->
        t
end

type t =
  { reg: Reg.t (* local info *)
  ; mem: Mem.t
  ; pc: PC.t
  ; control_deps: ControlDeps.t (* local info *)
  ; mutable vtmap: VTMap.t
  ; mutable visited_allocs: Node.Set.t (* heap-only *)
  ; mutable revisited_allocs: Node.Set.t (* heap-only *)
  ; replaced_values: ReplacedValMap.t (* symbol to concrete *)
  ; invalidated_values: AbsVal.t (* add-only *)
  ; assert_conds: AssertConds.t (* DNF constraints *)
  ; is_exceptional: bool
  ; is_conditional: bool (* for fault *)
  ; changed: Changed.t (* pre-condition for diff *)
  ; last_org: last_org
  ; abs_patches: AbsFault.t (* for fault *)
  ; id_use: IdUse.t (* for original *)
  ; loc_use: LocUse.t (* for original *)
  ; loc_def: LocDef.t (* for original *)
  ; important_param: AbsVal.t (* for precision *)
  ; current_ctxs: Contexts.t (* for diff, fault *)
  ; current_proc: Procname.t
  ; is_incomplete: bool }

and last_org = Original | Current of InstrNode.t * t | Past of InstrNode.t * t

let pp_last_org ~simple fmt = function
  | Original ->
      F.fprintf fmt "Original"
  | Current _ ->
      F.fprintf fmt "CurrentNode"
  | Past (node, _) when simple ->
      F.fprintf fmt "@[<v 2> - LastNode:@,   %a@]" InstrNode.pp node
  | Past (node, ostate) ->
      F.fprintf fmt
        "@[<v 2> - LastNode:@,   %a@, - OrgReg:@,   %a@, - OrgMem:@,   %a@, - LocDef:   %a@]"
        InstrNode.pp node Reg.pp ostate.reg Mem.pp ostate.mem LocDef.pp ostate.loc_def


let pp_sig fmt {is_exceptional; abs_patches; current_ctxs; changed; last_org} =
  let exn_sig = if is_exceptional then "E" else "N" in
  let org_str = match last_org with Past _ -> "P" | Current _ -> "C" | Original -> "O" in
  F.fprintf fmt "%s%s(abs_patches: %a, Contexts: %a, Changed: %a)" exn_sig org_str AbsFault.pp
    abs_patches Contexts.pp current_ctxs Changed.pp changed


let pp_full fmt
    { reg
    ; mem
    ; vtmap
    ; visited_allocs
    ; revisited_allocs
    ; replaced_values
    ; invalidated_values
    ; assert_conds
    ; is_exceptional
    ; is_conditional
    ; changed
    ; last_org
    ; abs_patches
    ; id_use
    ; loc_use
    ; loc_def
    ; current_ctxs
    ; current_proc
    ; control_deps
    ; important_param
    ; is_incomplete } : unit =
  F.fprintf fmt
    "@[<v 2>  - Register:@,\
    \   %a@,\
    \ - Memory:@,\
    \   %a@,\
    \ - Val-Type Map:@,\
    \   %a@,\
    \ - Is Exceptional? Is Conditional? Is Incomplete? @,\
    \   %b,%b,%b @,\
    \ - abs_patches:@,\
    \   %a @,\
    \ - Changed@,\
    \   %a @,\
    \ - Control Deps@,\
    \   %a @,\
    \ - Id - Used Symbol:@,\
    \   %a @,\
    \ - Loc - Used Symbol:@,\
    \   %a @,\
    \ - Loc - Defined location :@,\
    \   %a @,\
    \ - Last Node Equals To Orginal State:@,\
    \   %a @,\
    \ - Visited Allocsites:@,\
    \   %a@,\
    \ - Revisited Allocsites:@,\
    \   %a@,\
    \ - Replaced Values, Invalidated Values:@,\
    \   %a, %a@,\
    \ - Important parameter:@,\
    \   %a@,\
    \ - Current context, procedure@,\
    \   %a, %a@,\
    \ - Assert Conditions:@,\
    \   %a@]\n"
    Reg.pp reg Mem.pp mem VTMap.pp vtmap is_exceptional is_conditional is_incomplete AbsFault.pp
    abs_patches Changed.pp changed ControlDeps.pp control_deps IdUse.pp id_use LocUse.pp loc_use
    LocDef.pp loc_def (pp_last_org ~simple:false) last_org Node.Set.pp visited_allocs Node.Set.pp
    revisited_allocs ReplacedValMap.pp replaced_values AbsVal.pp invalidated_values AbsVal.pp
    important_param Contexts.pp current_ctxs Procname.pp current_proc AssertConds.pp assert_conds


let pp_simple fmt
    { reg
    ; mem
    ; vtmap
    ; assert_conds
    ; is_exceptional
    ; is_conditional
    ; changed
    ; control_deps
    ; last_org
    ; abs_patches
    ; current_ctxs
    ; current_proc
    ; important_param
    ; is_incomplete } : unit =
  F.fprintf fmt
    "@[<v 2>  - Register:@,\
    \   %a@,\
    \ - Memory:@,\
    \   %a@,\
    \ - Val-Type Map:@,\
    \   %a@,\
    \ - Is Exceptional? Is Conditional? Is Incomplete? @,\
    \   %b,%b,%b @,\
    \ - abs_patches:@,\
    \   %a @,\
    \ - Changed@,\
    \   %a @,\
    \ - Control Deps@,\
    \   %a @,\
    \ - Last Node Equals To Orginal State:@,\
    \   %a @,\
    \ - Important parameter:@,\
    \   %a@,\
    \ - Current context, procedure:@,\
    \   %a, %a@,\
    \ - Assert Conditions:@,\
    \   %a@]\n"
    Reg.pp reg Mem.pp mem VTMap.pp vtmap is_exceptional is_conditional is_incomplete AbsFault.pp
    abs_patches Changed.pp changed ControlDeps.pp control_deps (pp_last_org ~simple:true) last_org
    AbsVal.pp important_param Contexts.pp current_ctxs Procname.pp current_proc AssertConds.pp
    assert_conds


let pp = if Config.debug_level_analysis > 2 then pp_full else pp_simple

let leq ~lhs ~rhs =
  (* Optimization in disjunctive analysis: prune redundant states *)
  phys_equal lhs rhs


let bottom =
  { reg= Reg.bottom
  ; mem= Mem.bottom
  ; pc= PC.empty
  ; vtmap= VTMap.bottom
  ; visited_allocs= Node.Set.empty
  ; revisited_allocs= Node.Set.empty
  ; replaced_values= ReplacedValMap.empty
  ; invalidated_values= AbsVal.empty
  ; assert_conds= AssertConds.empty
  ; is_exceptional= false
  ; is_conditional= false
  ; is_incomplete= false
  ; changed= Changed.empty
  ; id_use= IdUse.empty
  ; loc_use= LocUse.empty
  ; loc_def= LocDef.empty
  ; last_org= Original
  ; abs_patches= None
  ; current_proc= Procname.empty_block
  ; current_ctxs= Contexts.empty
  ; control_deps= ControlDeps.bottom
  ; important_param= AbsVal.empty }


let is_bottom {reg; mem; pc} = Reg.is_bottom reg && Mem.is_bottom mem && PC.is_bottom pc

(** Basic Queries *)

let is_unknown_id {reg} id = not (Reg.mem id reg)

let is_exceptional {is_exceptional} = is_exceptional

let is_conditional {is_conditional} = is_conditional

let is_trivial_state = function
  | _ when Config.sprint_exnchecker ->
      false
  | {last_org= Current _; mem; reg} when Reg.is_bottom reg && Mem.is_bottom mem ->
      true
  | _ ->
      false


let has_skip_fault {abs_patches} =
  match abs_patches with
  | Some abs_patches ->
      Fault.Set.exists
        (function {desc} -> ( match desc with ShouldSkip -> true | _ -> false ))
        abs_patches
  | None ->
      false


let has_dummy_ctx {current_ctxs} = Contexts.mem Context.dummy current_ctxs

let is_dummy_ctx {current_ctxs} = Contexts.equal (Contexts.singleton Context.dummy) current_ctxs

let string_value_field =
  Fieldname.make (Typ.Name.Java.from_string "java.lang.StringBuilder") "value"


let read_loc_opt astate l : AbsVal.t option =
  match (Mem.find_opt l astate.mem, l) with
  | Some v, _ ->
      Some v
  | None, Loc.TempVar pv when is_catch_var pv ->
      Some AbsVal.top_primitive
  | None, l when Loc.is_heap_pred ~pred:Val.is_null l ->
      (* invalid values: read value from null.f *)
      Some AbsVal.bottom
  | None, Loc.Field (SymHeap (VString _ as v), fn) when (Fieldname.equal fn) string_value_field ->
      (* read value from "str".value -> "str" *)
      Some (AbsVal.singleton v)
  | None, Loc.SymHeap v when Val.is_extern v || Loc.is_abstract_heap l ->
      (* value of extern-symbol: absfun of that *)
      Some (AbsVal.singleton v)
  | None, Loc.Field (SymHeap v, fn) when Val.is_extern v ->
      (* field of extern-symbol: absfun of that *)
      let value = Val.make_uninterpret (Models.field_of fn) [v] in
      Some (AbsVal.singleton value)
  | None, Loc.Index (SymHeap v, _) when Val.is_extern v ->
      (* index of extern-symbol: absfun of that *)
      let value = Val.make_absfun Models.index_of [v] in
      Some (AbsVal.singleton value)
  | None, Loc.Field (SymHeap (VSymbol _), _)
  | None, Loc.Field (Var _, _)
  | None, Loc.SymHeap (VSymbol _)
  | None, Loc.Index (SymHeap (VSymbol _), _) -> (
    match Loc.to_symbol_opt l with
    | Some s when Symbol.is_global s ->
        Some (AbsVal.singleton (Val.VSymbol s))
    | Some s ->
        (* read value from param -> $param *)
        Some (AbsVal.singleton (Val.VSymbol s))
    | None ->
        (* read value from unknown location *)
        None )
  | None, _ ->
      None


let read_loc_default astate l : AbsVal.t =
  match (read_loc_opt astate l, l) with
  | Some v, _ ->
      v
  | None, _ when Loc.is_primitive l ->
      (* L.d_printfln "[WARNING]: read from primitive %a@." Loc.pp l ; *)
      AbsVal.bottom
  | None, Loc.Field (SymHeap v, fn) ->
      (* HEURISTICS: always symbolize value of unknown field *)
      (* L.d_printfln "[WARNING]: could not properly read value of %a" Loc.pp l ; *)
      let value = Val.make_uninterpret (Models.field_of fn) [v] in
      AbsVal.singleton value
  | None, Loc.Index (SymHeap v, _) ->
      (* HEURISTICS: always symbolize value of unknown field *)
      (* L.d_printfln "[WARNING]: could not properly read value of %a" Loc.pp l ; *)
      let value = Val.make_absfun Models.index_of [v] in
      AbsVal.singleton value
  | None, _ ->
      (* FIXME: remove bottom and report *)
      L.debug L.Analysis L.Quiet "[WARNING]: could not read value from unknown location %a@.(%a@)"
        Loc.pp l pp_sig astate ;
      AbsVal.bottom


let read_loc astate (l, diff) =
  match (astate.last_org, diff) with
  | Original, _ ->
      let value = read_loc_default astate l in
      let symbolic_diff = Disjunct.of_values value |> SymDiff.of_uses |> SymDiff.join diff in
      (value, LocUse.find l astate.loc_use |> SymDiff.of_uses |> SymDiff.join symbolic_diff)
  | _, _ when Mem.mem l astate.mem ->
      (read_loc_default astate l, SymDiff.diff)
  | Current (_, original), _ when Mem.mem l original.mem ->
      (read_loc_default original l, diff)
  | Past (_, original), _ when Mem.mem l original.mem ->
      (read_loc_default original l, SymDiff.diff)
  | Current _, _ ->
      (read_loc_default astate l, diff)
  | Past _, _ ->
      (read_loc_default astate l, SymDiff.diff)


let read_loc astate (l, diff) =
  if Config.sprint_exnchecker then
    match l with Loc.Var _ | Loc.TempVar _ -> read_loc astate (l, SymDiff.diff) | _ -> DiffVal.top
  else read_loc astate (l, diff)


let type_checker astate v = VTMap.find_opt v astate.vtmap

let is_sat_assert astate =
  AssertCond.is_sat ~get_type:(type_checker astate) ~revisited_allocs:astate.revisited_allocs


let is_satisfiable astate = AssertConds.for_all (is_sat_assert astate) astate.assert_conds

let is_strong_updatable_val {revisited_allocs} v = Val.is_strong_updatable ~revisited_allocs v

let is_strong_updatable_loc {revisited_allocs} l = Loc.is_strong_updatable ~revisited_allocs l

let is_original astate = match astate.last_org with Original -> true | _ -> false

let has_past_original astate = match astate.last_org with Past _ -> true | _ -> false

let is_org_value astate _ diff =
  match (diff, astate.last_org) with
  | _, Past _ ->
      false
  | SymDiff.Diff, _ ->
      false
  | SymDiff.Org _, _ ->
      true


let find_dynamic_exprs ?(dyninfo = DynInfo.from_marshal ()) astate instr_node =
  let instr = InstrNode.get_instr instr_node in
  let result =
    if is_prune_instr instr then
      match DynInfo.get_br_info ~dyninfo astate.current_ctxs instr_node with
      | AbsBool.V _ as v ->
          Some v
      | _ ->
          None
    else
      match DynInfo.get_die_info ~dyninfo astate.current_ctxs instr_node with
      | AbsBool.V _ as v ->
          Some v
      | _ ->
          None
  in
  match result with Some v -> v | None -> ControlDeps.find instr_node astate.control_deps


let add_control_deps instr_node is_org_value astate =
  if is_original astate || is_org_value || has_past_original astate || Config.sprint_exnchecker then
    astate
  else
    match (Node.get_instr instr_node, ControlDeps.find instr_node astate.control_deps) with
    | Sil.Prune (bexp, _, _, _), _ when Fault.is_hole bexp ->
        astate
    | _, (AbsBool.V _ as abool) ->
        {astate with control_deps= ControlDeps.update instr_node abool astate.control_deps}
    | _ ->
        astate


let set_conditional astate = {astate with is_conditional= true}

let unset_conditional astate = {astate with is_conditional= false}

let should_execute node instr astate =
  if Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.Exit_node then true
  else if is_exceptional astate then
    Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.exn_handler_kind
  else if is_conditional astate then
    match astate.abs_patches with
    | Some abs_patches -> (
      match Fault.Set.choose abs_patches with
      | {desc= ShouldSkip; loc= Range (_, Before to_node)} ->
          InstrNode.equal_except_vflag (Node.of_pnode node instr) to_node
      | {desc= MissingErrorHandling `Return} ->
          Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.Exit_node
      | _ ->
          false )
    | None ->
        L.(die InternalError) "Invalid fault"
  else true


let is_dynamic_normal ?(dyninfo = DynInfo.from_marshal ()) astate instr_node =
  match find_dynamic_exprs ~dyninfo astate instr_node with
  | V true ->
      `Yes
  | V false ->
      `No
  | Bot when has_past_original astate ->
      `No
  | Bot when is_call_instr (Node.get_instr instr_node) ->
      `Yes
  | _ ->
      `Unknown


let is_dynamic_throw ?(dyninfo = DynInfo.from_marshal ()) astate instr_node =
  match find_dynamic_exprs ~dyninfo astate instr_node with
  | V false ->
      `Yes
  | V true ->
      `No
  | _ ->
      `Unknown


let read_locs astate (locs, diff) =
  Loc.Set.fold (fun l -> read_loc astate (l, diff) |> DiffVal.join) locs DiffVal.empty


let read_typ {vtmap} v = VTMap.find v vtmap

let read_typ_of_vals {vtmap} vals = VTMap.find_vals vals vtmap

let equal_values astate v = PC.equal_values astate.pc v

(*  *)
let inequal_values astate v = PC.inequal_values astate.pc v

let is_valid_pc astate pathcond = PC.is_valid pathcond astate.pc

let all_values
    {reg; pc; mem; vtmap; replaced_values; invalidated_values; assert_conds; loc_use; changed} =
  (* seems too inefficient *)
  let pc_values = PC.all_values pc |> AbsVal.of_list in
  let mem_values =
    Mem.fold
      (fun l vals ->
        match l with
        | Loc.Field (Loc.SymHeap v, _) | Loc.Index (Loc.SymHeap v, _) | Loc.SymHeap v ->
            AbsVal.union (AbsVal.singleton v) vals |> AbsVal.union
        | _ ->
            AbsVal.union vals )
      mem AbsVal.empty
  in
  let reg_values = Reg.fold (fun _ vals -> AbsVal.union vals) reg AbsVal.empty in
  let replaced_values =
    ReplacedValMap.fold (fun v1 _ -> AbsVal.set_add v1) replaced_values AbsVal.empty
  in
  let invalidated_values = AbsVal.fold AbsVal.set_add invalidated_values AbsVal.empty in
  let vtmap_values = VTMap.fold (fun v _ -> AbsVal.set_add v) vtmap AbsVal.empty in
  let assert_values =
    AssertConds.fold
      (fun (v1, v2, _, _) acc -> AbsVal.union v1 acc |> AbsVal.union v2)
      assert_conds AbsVal.empty
  in
  let used_values =
    LocUse.fold
      (fun l uses ->
        Loc.get_vals l @ List.map ~f:(fun s -> Val.VSymbol s) (Disjunct.elements uses)
        |> AbsVal.of_list |> AbsVal.union )
      loc_use AbsVal.empty
  in
  let control_symbols = Changed.get_values changed in
  pc_values |> AbsVal.union mem_values |> AbsVal.union reg_values |> AbsVal.union replaced_values
  |> AbsVal.union invalidated_values |> AbsVal.union vtmap_values |> AbsVal.union assert_values
  |> AbsVal.union used_values |> AbsVal.union control_symbols |> AbsVal.get_subvalues


let is_abstract astate =
  Mem.exists (fun l v -> Loc.is_abstract l || AbsVal.exists Val.is_abstract v) astate.mem


let get_important_type astate =
  AbsVal.fold (fun v acc -> read_typ astate v :: acc) astate.important_param []


let get_return_type astate =
  let program = Program.from_marshal () in
  let procname = astate.current_proc in
  let procdesc = Program.pdesc_of program procname in
  let ret_var = Procdesc.get_ret_var procdesc in
  let ret_loc = Loc.of_pvar ret_var in
  match Mem.find_opt ret_loc astate.mem with
  | Some v ->
      Some (read_typ_of_vals astate v)
  | None ->
      None


let is_equal_type lhs rhs =
  AbsVal.for_all (fun v -> AbsTyp.equal (read_typ lhs v) (read_typ rhs v)) lhs.important_param


let is_equal_context lhs rhs = not (Contexts.disjoint lhs.current_ctxs rhs.current_ctxs)

let is_equal_return_typ lhs rhs =
  let program = Program.from_marshal () in
  let procname = lhs.current_proc in
  let procdesc = Program.pdesc_of program procname in
  let ret_var = Procdesc.get_ret_var procdesc in
  let ret_loc = Loc.of_pvar ret_var in
  match (Mem.find_opt ret_loc lhs.mem, Mem.find_opt ret_loc rhs.mem) with
  | Some v1, Some v2 ->
      let abstyp1, abstyp2 = (read_typ_of_vals lhs v1, read_typ_of_vals rhs v2) in
      AbsTyp.equal abstyp1 abstyp2 || AbsTyp.is_top abstyp1 || AbsTyp.is_top abstyp2
  | _ ->
      true


let is_original_of ~astate ostate =
  let debug_if_past_fail msg b =
    ( match astate.last_org with
    | Past _ when (not b) && Config.debug_level_analysis > 2 ->
        L.d_printfln "\n    %a not original of %a because of %s" pp_sig astate pp_sig ostate msg
    | _ ->
        () ) ;
    b
  in
  is_original ostate
  && Bool.equal astate.is_exceptional ostate.is_exceptional
  && ControlDeps.is_covered astate.control_deps ~org:ostate.control_deps
     |> debug_if_past_fail "controlDeps"
  && is_equal_context astate ostate |> debug_if_past_fail "contexts"
  && is_equal_type astate ostate |> debug_if_past_fail "important type"
  && is_equal_return_typ astate ostate |> debug_if_past_fail "return type"


let match_diff_original diffs orgs =
  let orgs = List.filter ~f:(not <<< has_dummy_ctx) orgs in
  let matched, unmatched =
    List.fold orgs ~init:([], diffs) ~f:(fun (acc, diffs_to_match) org_state ->
        let matched, unmatched =
          List.partition_tf diffs_to_match ~f:(fun astate -> is_original_of ~astate org_state)
        in
        let matched = List.map matched ~f:(fun astate -> (Some org_state, astate)) in
        (matched @ acc, unmatched) )
  in
  matched @ List.map unmatched ~f:(fun astate -> (None, astate))


let set_diff instr_node astate =
  if Config.sprint_exnchecker || Config.sprint_no_test then
    { astate with
      reg= astate.reg
    ; mem= astate.mem
    ; loc_use= LocUse.empty
    ; id_use= IdUse.empty
    ; loc_def= LocDef.empty
    ; control_deps= astate.control_deps
    ; last_org= Past (instr_node, astate) }
  else
    { astate with
      reg= Reg.empty
    ; mem= Mem.empty
    ; loc_use= LocUse.empty
    ; id_use= IdUse.empty
    ; loc_def= LocDef.empty
    ; control_deps= astate.control_deps
    ; last_org= Current (instr_node, astate) }


let set_past instr_node ~ostate astate = {astate with last_org= Past (instr_node, ostate)}

let astate_with_merged_mem astate =
  match astate.last_org with
  | Original ->
      astate
  | Current (_, original_astate) | Past (_, original_astate) ->
      { astate with
        mem=
          Mem.fold
            (fun l v acc -> if Mem.mem l astate.mem then acc else Mem.strong_update l v acc)
            original_astate.mem astate.mem
      ; last_org= Original }


let _store_loc ~is_weak instr_node loc_values uses astate =
  let loc_use, loc_def =
    if is_original astate && not (is_dummy_ctx astate) then
      List.fold loc_values ~init:(astate.loc_use, astate.loc_def)
        ~f:(fun (acc_lu, acc_ld) (l', _) ->
          ( LocUse.update ~is_weak:true l' uses acc_lu
          , LocDef.update ~is_weak:true l' instr_node acc_ld ) )
    else (astate.loc_use, astate.loc_def)
  in
  let mem =
    List.fold loc_values ~init:astate.mem ~f:(fun acc (l, vals) -> Mem.update ~is_weak l vals acc)
  in
  {astate with loc_use; loc_def; mem}


(** Update memory *)
let store_loc ?(is_weak = false) instr_node l (v, symdiff) astate : t =
  let uses = SymDiff.uses_of symdiff in
  (* L.d_printfln "update %a by %a" Loc.pp l Disjunct.pp uses ; *)
  (* if Loc.is_unknown l then
     L.progress "[UNKNOWN]: store value to unknown value (%a)@.%a@." InstrNode.pp instr_node pp_sig astate ; *)
  if Loc.is_primitive l then astate
  else if match l with Loc.SymHeap (VHeap _) -> true | _ -> false then (
    L.d_printfln "[UNKNOWN]: store value to heap (%a)@.%a@." InstrNode.pp instr_node pp_sig astate ;
    astate )
  else
    let def = Node.ASet.singleton instr_node in
    let uses = Disjunct.union (Disjunct.of_values v) uses in
    let compute_loc_vals_to_update absheap =
      let result =
        match (l, astate.last_org) with
        (* FIXME:
           | Loc.SymHeap (VSymbol (base, accs, is_abstract)), _ -> (
              match List.rev accs with
              | Symbol.Field fn :: rest ->
                  let updated_loc = Loc.Field (Loc.SymHeap (VSymbol (base, List.rev rest, false)), fn) in
                  [(updated_loc, AbsVal.singleton (VSymbol (base, accs, is_abstract)))]
              | Symbol.Index _ :: rest ->
                  let updated_loc =
                    Loc.Index (Loc.SymHeap (VSymbol (base, List.rev rest, false)), Val.top_primitive)
                  in
                  [(updated_loc, AbsVal.singleton (VSymbol (base, accs, is_abstract)))]
              | [] ->
                  L.(die InternalError) "empty symbol could not be abstract" ) *)
        | Loc.SymHeap (VAbsFun (_, [(VHeap _ as v)])), (Current (_, org_state) | Past (_, org_state))
          ->
            let absheap = AbsVal.set_add v (AbsVal.singleton absheap) in
            Mem.fold
              (fun l vals acc -> if AbsVal.disjoint absheap vals then acc else (l, vals) :: acc)
              org_state.mem []
        | _, (Current (_, org_state) | Past (_, org_state)) ->
            Mem.fold
              (fun l vals acc -> if AbsVal.mem absheap vals then (l, vals) :: acc else acc)
              org_state.mem []
        | _, Original ->
            []
      in
      List.iter result ~f:(fun (loc, vals) ->
          L.d_printfln "update %a that points-to abstract value: %a" Loc.pp loc AbsVal.pp vals ) ;
      result
    in
    match astate.last_org with
    (* TODO: refine this HEURISTICS *)
    | _ when Loc.is_abstract_heap l && Config.sprint_exnchecker ->
        let absheap = Loc.get_vals l |> List.hd_exn in
        let loc_values_to_update = compute_loc_vals_to_update absheap in
        _store_loc ~is_weak:true def loc_values_to_update uses astate
    | (Current _ | Past _) when Loc.is_abstract_heap l && SymDiff.is_diff symdiff ->
        let absheap = Loc.get_vals l |> List.hd_exn in
        let loc_values_to_update = compute_loc_vals_to_update absheap in
        if List.is_empty loc_values_to_update then
          _store_loc ~is_weak:true def [(l, AbsVal.top)] uses astate
        else _store_loc ~is_weak:true def loc_values_to_update uses astate
    | Original when Loc.is_abstract_heap l ->
        _store_loc ~is_weak:true def [(l, AbsVal.top)] uses astate (* astate *)
    | Original ->
        let is_weak = is_weak || not (is_strong_updatable_loc astate l) in
        _store_loc ~is_weak def [(l, v)] uses astate
    | (Current _ | Past _) when SymDiff.is_diff symdiff ->
        let is_weak = is_weak || not (is_strong_updatable_loc astate l) in
        _store_loc ~is_weak def [(l, v)] uses astate
    | (Current _ | Past _) when (not is_weak) && is_strong_updatable_loc astate l ->
        (* remove changes (e.g., this.f = X; this.f = org; => no changes) *)
        {astate with mem= Mem.remove l astate.mem}
    | Current _ | Past _ ->
        astate


let store_locs instr_node locs (v, symdiff) astate : t =
  let symdiff = if has_past_original astate then SymDiff.diff else symdiff in
  if Int.equal (Loc.Set.cardinal locs) 1 then
    Loc.Set.fold
      (fun l ->
        if is_strong_updatable_loc astate l then store_loc instr_node ~is_weak:false l (v, symdiff)
        else store_loc instr_node ~is_weak:true l (v, symdiff) )
      locs astate
  else Loc.Set.fold (fun l -> store_loc instr_node ~is_weak:true l (v, symdiff)) locs astate


let store_reg id (v, symdiff) astate =
  let symdiff = if has_past_original astate then SymDiff.diff else symdiff in
  if SymDiff.is_diff symdiff || is_original astate then
    let id_use =
      let uses = SymDiff.uses_of symdiff in
      if Disjunct.is_empty uses || (not (is_original astate)) || is_dummy_ctx astate then
        astate.id_use
      else IdUse.strong_update id uses astate.id_use
    in
    {astate with reg= Reg.strong_update id v astate.reg; id_use}
  else astate


let store_reg_weak id (v, symdiff) astate =
  let symdiff = if has_past_original astate then SymDiff.diff else symdiff in
  if SymDiff.is_diff symdiff || is_original astate then
    let id_use =
      let uses = SymDiff.uses_of symdiff in
      if Disjunct.is_empty uses || (not (is_original astate)) || is_dummy_ctx astate then
        astate.id_use
      else IdUse.weak_update id uses astate.id_use
    in
    {astate with reg= Reg.weak_update id v astate.reg; id_use}
  else astate


let store_typ vals abstyp astate =
  match AbsVal.is_singleton_or_more vals with
  | Singleton _ when Typ.is_void (AbsTyp.typ_of abstyp) ->
      (* type of instruction could be ill-written *)
      astate
  | Singleton v when is_strong_updatable_val astate v ->
      {astate with vtmap= VTMap.strong_update v abstyp astate.vtmap}
  | Singleton v ->
      {astate with vtmap= VTMap.weak_update v abstyp astate.vtmap}
  | Empty | More ->
      astate


(* remove or replace state *)
let update_state astate ~pc ~mem ~reg ~vtmap ~invalidated_values ~replaced_values ~assert_conds
    ~visited_allocs ~revisited_allocs ~loc_use ~loc_def ~last_org =
  (* components which have AbsVal.t, they are all carefully updated *)
  { reg
  ; mem
  ; pc
  ; vtmap
  ; visited_allocs
  ; revisited_allocs
  ; replaced_values
  ; invalidated_values
  ; assert_conds
  ; loc_use
  ; loc_def
  ; last_org
  ; id_use= astate.id_use
  ; changed= astate.changed
  ; is_exceptional= astate.is_exceptional
  ; is_conditional= astate.is_conditional
  ; is_incomplete= astate.is_incomplete
  ; abs_patches= astate.abs_patches
  ; current_proc= astate.current_proc
  ; current_ctxs= astate.current_ctxs
  ; control_deps= astate.control_deps
  ; important_param= astate.important_param }


let remove_unreachable_heaps astate vals =
  L.d_printfln "found unreachabled heaps: %a" AbsVal.pp vals ;
  let is_reachable_loc l =
    match Loc.get_val_opt l with Some v' -> not (AbsVal.mem v' vals) | None -> true
  in
  let heap_alloc_node =
    AbsVal.fold
      (function Val.VHeap n -> Node.Set.add n | _ -> L.(die InternalError) "remove non-heap value")
      vals Node.Set.empty
  in
  let reg = astate.reg in
  let mem = Mem.filter (fun l _ -> is_reachable_loc l) astate.mem in
  let pc = astate.pc in
  let vtmap = AbsVal.fold VTMap.remove vals astate.vtmap in
  let visited_allocs = Node.Set.fold Node.Set.remove heap_alloc_node astate.visited_allocs in
  let revisited_allocs = Node.Set.fold Node.Set.remove heap_alloc_node astate.revisited_allocs in
  let replaced_values = astate.replaced_values in
  let invalidated_values = astate.invalidated_values in
  let assert_conds = astate.assert_conds in
  let loc_def = LocDef.filter (fun l _ -> is_reachable_loc l) astate.loc_def in
  let loc_use = LocUse.filter (fun l _ -> is_reachable_loc l) astate.loc_use in
  let last_org = (* TODO: *) astate.last_org in
  update_state astate ~reg ~mem ~pc ~vtmap ~visited_allocs ~revisited_allocs ~replaced_values
    ~invalidated_values ~assert_conds ~loc_def ~loc_use ~last_org


let filter_unreachable_heaps astate vals vars =
  let is_pointed_by_mem =
    Mem.exists (fun l v ->
        match l with
        | (Loc.TempVar pv | Loc.Var pv) when List.mem vars ~equal:Var.equal (Var.of_pvar pv) ->
            false
        | _ ->
            not (AbsVal.disjoint v vals) )
  in
  let is_pointed_by_reg =
    Reg.exists (fun id v ->
        if List.mem vars ~equal:Var.equal (Var.of_id id) then false
        else not (AbsVal.disjoint v vals) )
  in
  let is_reachable =
    match astate.last_org with
    | Current (_, ostate) | Past (_, ostate) ->
        is_pointed_by_mem astate.mem || is_pointed_by_reg astate.reg || is_pointed_by_mem ostate.mem
        || is_pointed_by_reg ostate.reg
    | Original ->
        is_pointed_by_mem astate.mem || is_pointed_by_reg astate.reg
  in
  if is_reachable then AbsVal.empty else vals


let remove_id astate id =
  if Reg.mem id astate.reg then
    {astate with reg= Reg.remove id astate.reg; id_use= IdUse.remove id astate.id_use}
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_pvar astate ~pv =
  let pvar_loc = Loc.of_pvar pv in
  if Mem.mem pvar_loc astate.mem then
    { astate with
      mem= Mem.remove pvar_loc astate.mem
    ; loc_use= LocUse.remove pvar_loc astate.loc_use
    ; loc_def= LocDef.remove pvar_loc astate.loc_def }
  else (* OPTIMIZATION: to enable physical equality *) astate


let remove_var astate = function
  | Var.ProgramVar pv ->
      remove_pvar astate ~pv
  | Var.LogicalVar id ->
      remove_id astate id


let remove_temps astate vars =
  let astate, vals_pointed_by_vars =
    List.fold vars ~init:(astate, AbsVal.empty) ~f:(fun (astate, heaps) var ->
        match (var, astate.last_org) with
        | Var.ProgramVar pv, Original ->
            (* TODO: could remove unreachable locations here *)
            let vals = Mem.find (Loc.of_pvar pv) astate.mem in
            (remove_pvar astate ~pv, AbsVal.union heaps vals)
        | Var.ProgramVar pv, (Current _ | Past _) when Mem.mem (Loc.of_pvar pv) astate.mem ->
            let vals = Mem.find (Loc.of_pvar pv) astate.mem in
            (remove_pvar astate ~pv, AbsVal.union heaps vals)
        | Var.ProgramVar pv, (Current (_, org_state) | Past (_, org_state)) ->
            (* l[Top] -> v in astate, but tmp -> l only in org_state *)
            let vals = Mem.find (Loc.of_pvar pv) org_state.mem in
            (remove_pvar astate ~pv, AbsVal.union heaps vals)
        | Var.LogicalVar id, Original ->
            (remove_id astate id, AbsVal.union heaps (Reg.find id astate.reg))
        | Var.LogicalVar id, (Current _ | Past _) when Reg.mem id astate.reg ->
            (remove_id astate id, AbsVal.union heaps (Reg.find id astate.reg))
        | Var.LogicalVar id, (Current (_, org_state) | Past (_, org_state)) ->
            (* l[Top] -> v in astate, but id -> l only in org_state *)
            (astate, AbsVal.union heaps (Reg.find id org_state.reg)) )
  in
  let heaps_pointed_by_vars = AbsVal.filter Val.is_heap vals_pointed_by_vars in
  match astate.last_org with
  | _ when AbsVal.is_empty heaps_pointed_by_vars ->
      astate
  | Original | Current _ ->
      filter_unreachable_heaps astate heaps_pointed_by_vars vars |> remove_unreachable_heaps astate
  | Past (node, ostate) ->
      let last_org = Past (node, List.fold vars ~init:ostate ~f:remove_var) in
      filter_unreachable_heaps {astate with last_org} heaps_pointed_by_vars vars
      |> remove_unreachable_heaps astate


let remove_locals astate ~pdesc =
  let pname = Procdesc.get_proc_name pdesc in
  let ret_var = Procdesc.get_ret_var pdesc in
  let formal_pvars = Procdesc.get_pvar_formals pdesc |> List.map ~f:fst in
  let locals =
    Procdesc.get_locals pdesc |> List.map ~f:(fun ProcAttributes.{name} -> Pvar.mk name pname)
  in
  List.fold ((ret_var :: formal_pvars) @ locals) ~init:astate ~f:(fun acc pv -> remove_pvar acc ~pv)


let is_invalid astate =
  PC.is_invalid astate.pc
  || (* TODO: check whther it is correct *)
  Mem.exists (fun l _ -> Loc.is_invalid l) astate.mem


let replace_value astate ~(src : Val.t) ~(dst : Val.t) : t =
  L.d_printfln " - replace value from %a to %a" Val.pp src Val.pp dst ;
  let pc = astate.pc in
  let mem = Mem.replace_value ~src ~dst astate.mem in
  let reg = Reg.map (AbsVal.replace_sub ~src ~dst) astate.reg in
  let vtmap =
    if Val.is_generatable dst then
      VTMap.fold
        (fun v t -> VTMap.weak_update (Val.replace_sub ~src ~dst v) t)
        astate.vtmap astate.vtmap
    else astate.vtmap
  in
  let invalidated_values = (* TODO: really? *) astate.invalidated_values in
  let replaced_values = ReplacedValMap.add src dst astate.replaced_values in
  let assert_conds = (* no allocsite *) astate.assert_conds in
  let loc_use =
    LocUse.fold (fun l s -> LocUse.add (Loc.replace_heap ~src ~dst l) s) astate.loc_use LocUse.empty
  in
  let loc_def =
    LocDef.fold (fun l d -> LocDef.add (Loc.replace_heap ~src ~dst l) d) astate.loc_def LocDef.empty
  in
  let last_org = (* TODO: currently replace_value is deprecated *) astate.last_org in
  update_state astate ~pc ~mem ~reg ~vtmap ~replaced_values ~invalidated_values ~assert_conds
    ~loc_use ~loc_def ~visited_allocs:astate.visited_allocs
    ~revisited_allocs:astate.revisited_allocs ~last_org


let set_current_proc astate proc_name = {astate with current_proc= proc_name}

let set_exception astate = {astate with is_exceptional= true}

let set_ctx astate ctxs = {astate with current_ctxs= ctxs}

let set_assertion assert_cond astate =
  let v1, v2, _, _ = assert_cond in
  let has_hole = AbsVal.exists (function Val.VFreshSymbol _ -> true | _ -> false) in
  L.d_printfln "try to append assertion %a" AssertCond.pp assert_cond ;
  if Config.sprint_exnchecker then astate
  else if AbsVal.exists Val.is_abstract v1 || AbsVal.exists Val.is_abstract v2 then astate
  else if has_hole v1 || has_hole v2 then astate
  else {astate with assert_conds= AssertConds.add assert_cond astate.assert_conds}


let add_changed instr_node ~is_org_flow symdiff astate : t option =
  let uses = SymDiff.uses_of symdiff in
  let is_org_value = not (SymDiff.is_diff symdiff) in
  let add_reg_changed original_astate =
    Reg.fold
      (fun id v acc ->
        if Reg.mem id acc.reg then acc
        else if Disjunct.disjoint (IdUse.find id original_astate.id_use) uses then acc
        else store_reg id (v, SymDiff.diff) acc )
      original_astate.reg
  in
  let add_mem_changed original_astate =
    Mem.fold
      (fun l v acc ->
        if Mem.mem l acc.mem then acc
        else if Disjunct.disjoint (LocUse.find l original_astate.loc_use) uses then acc
        else store_loc instr_node l (v, SymDiff.diff) acc )
      original_astate.mem
  in
  let is_org_value = if is_original astate then true else is_org_value in
  match astate.last_org with
  | _ when not (is_no is_org_flow) ->
      let _ = L.d_printfln "original flow" in
      Some astate
  | Current (_, ostate) when not is_org_value ->
      let _ = L.d_printfln "non-original flow, but non-original value" in
      Some (add_control_deps instr_node is_org_value astate |> set_past instr_node ~ostate)
  | Past _ when not is_org_value ->
      let _ = L.d_printfln "non-original flow, but non-original value" in
      Some (add_control_deps instr_node is_org_value astate)
  | _ when Option.is_some astate.abs_patches ->
      let _ = L.d_printfln "non-original flow, original value with faulty state" in
      None
  | _ when Disjunct.is_empty uses ->
      let _ = L.d_printfln "non-original flow, original value with empty uses" in
      None
  | Past _ ->
      L.(die InternalError) "state with past original should have non-org-value"
  | Original when has_dummy_ctx astate ->
      None
  | Original ->
      let _ = L.d_printfln "non-original flow, original value with nonempty uses" in
      let result =
        {astate with changed= Changed.add_disjunct uses astate.changed}
        |> set_diff instr_node |> add_control_deps instr_node false
        |> set_past instr_node ~ostate:astate
        |> add_reg_changed astate |> add_mem_changed astate
      in
      Some result
  | Current (_, ostate) ->
      let _ = L.d_printfln "non-original flow, original value with nonempty uses" in
      let _ = L.d_printfln " add changed from non-original state" in
      let result =
        {astate with changed= Changed.add_disjunct uses astate.changed}
        |> add_control_deps instr_node false |> set_past instr_node ~ostate
        |> add_reg_changed ostate |> add_mem_changed ostate
      in
      Some result


let has_same_vtmap lhs rhs = Int.equal (VTMap.cardinal lhs.vtmap) (VTMap.cardinal rhs.vtmap)

let resolve_multiple_org astate ~ostate =
  if astate.is_conditional then astate
  else
    VTMap.fold
      (fun v abstyp acc ->
        if VTMap.mem v astate.vtmap then acc else store_typ (AbsVal.singleton v) abstyp acc )
      ostate.vtmap astate


let unwrap_exception astate = {astate with is_exceptional= false}

let set_fault astate ~fault = {astate with abs_patches= Some (Fault.Set.singleton fault)}

let set_abs_patches astate ~abs_patches = {astate with abs_patches}

let make_injective ~f arg_values =
  (* use Java function f where return_typ is specified *)
  AbsVal.make_injective f arg_values


let make_hole astate _ ~typ =
  (* FIXME: ignore loop *)
  (* CAUTION: do not change this to AbsVal.top *)
  let fresh_value = Val.make_hole Node.dummy in
  let abstyp = AbsTyp.make_instance typ in
  astate.vtmap <- VTMap.weak_update fresh_value abstyp astate.vtmap ;
  fresh_value


let make_fresh astate ~f ~typ instr_node =
  let fresh_value = Val.make_fresh_symbol f instr_node in
  let abstyp = AbsTyp.make_instance typ in
  if Node.Set.mem instr_node astate.visited_allocs then (
    astate.vtmap <- VTMap.weak_update fresh_value abstyp astate.vtmap ;
    astate.revisited_allocs <- Node.Set.add instr_node astate.revisited_allocs ;
    fresh_value )
  else (
    astate.vtmap <- VTMap.strong_update fresh_value abstyp astate.vtmap ;
    astate.visited_allocs <- Node.Set.add instr_node astate.visited_allocs ;
    fresh_value )


let make_allocsite astate ~abstyp instr_node =
  let allocsite = Val.make_allocsite instr_node in
  if Procname.is_java_class_initializer (InstrNode.get_proc_name instr_node) then (astate, allocsite)
  else
    let astate =
      if Node.Set.mem instr_node astate.visited_allocs then
        {astate with revisited_allocs= Node.Set.add instr_node astate.revisited_allocs}
      else {astate with visited_allocs= Node.Set.add instr_node astate.visited_allocs}
    in
    (store_typ (AbsVal.singleton allocsite) abstyp astate, allocsite)


let make_const _ _ v = (* DEPRECATED: now we don't track uniqueness of constant *) v

let make_uninterpret astate callee arg_diff_values =
  let arg_values, symdiffs = List.unzip arg_diff_values in
  let value = Val.make_uninterpret callee arg_values |> AbsVal.singleton in
  match astate.last_org with
  | Past _ ->
      (value, SymDiff.diff)
  | _ ->
      (value, List.fold symdiffs ~init:SymDiff.empty ~f:SymDiff.join)


let make_uninterpret_absval astate callee arg_diff_values =
  let arg_values, symdiffs = List.unzip arg_diff_values in
  let value = AbsVal.make_uninterpret callee arg_values in
  match astate.last_org with
  | Past _ ->
      (value, SymDiff.diff)
  | _ ->
      (value, List.fold symdiffs ~init:SymDiff.empty ~f:SymDiff.join)


let bind_extern_value astate _ ret_typ_id ~typ callee arg_diff_values =
  (* ret_id -> VFunction (callee, arg_values) *)
  let ret_id, _ = ret_typ_id in
  let diffval = make_uninterpret astate callee arg_diff_values in
  store_reg ret_id diffval astate |> store_typ (fst diffval) (AbsTyp.make_instance typ)


let bind_extern_value_absval _ ret_typ_id ~abstyp callee arg_diff_values astate =
  (* ret_id -> VFunction (callee, arg_values) *)
  let ret_id, _ = ret_typ_id in
  let diffval = make_uninterpret_absval astate callee arg_diff_values in
  store_reg ret_id diffval astate |> store_typ (fst diffval) abstyp


let bind_exn_extern_absval instr_node ret_var ~abstyp callee arg_diff_values astate =
  (* return -> Exn VFunction(callee, arg_values)
     typically, same exn could be returned for various inputs. So callee is not injective. *)
  let ret_loc = Loc.of_pvar ret_var in
  let callee_without_rettyp =
    (* IMPORTANT: remove return type information from callee procname *)
    Procname.from_string_c_fun (Procname.get_method callee)
  in
  let symdiff =
    List.unzip arg_diff_values |> snd |> List.fold ~init:SymDiff.empty ~f:SymDiff.join
  in
  (* ASSUMPTION: callee returns a single exception *)
  let diffval =
    make_uninterpret_absval astate callee_without_rettyp
      [(AbsVal.singleton (Val.VString "FL4APR_Exception"), symdiff)]
  in
  store_loc instr_node ret_loc diffval astate |> store_typ (fst diffval) abstyp |> set_exception


let bind_exn_extern instr_node ret_var ~exn_typ callee arg_diff_values astate =
  (* return -> Exn VFunction(callee, arg_values)
     typically, same exn could be returned for various inputs. So callee is not injective. *)
  let ret_loc = Loc.of_pvar ret_var in
  let callee_without_rettyp =
    (* IMPORTANT: remove return type information from callee procname *)
    Procname.from_string_c_fun (Procname.get_method callee)
  in
  let diffval = make_uninterpret astate callee_without_rettyp arg_diff_values in
  store_loc instr_node ret_loc diffval astate
  |> store_typ (fst diffval) (AbsTyp.make_instance exn_typ)
  |> set_exception


let throw_exn instr_node ret_var ~exn_typ_str astate =
  let exn_typ = AbsTyp.typ_from_string exn_typ_str in
  let exn_callee = Procname.from_string_c_fun exn_typ_str in
  bind_exn_extern instr_node ret_var ~exn_typ exn_callee [] astate


let throw_err instr_node ret_var ~exn_typ_str astate =
  let exn_typ = AbsTyp.typ_from_string exn_typ_str in
  let exn_callee = Procname.from_string_c_fun exn_typ_str in
  bind_exn_extern instr_node ret_var ~exn_typ exn_callee [(Val.zero, SymDiff.diff)] astate


let is_equal_sat astate =
  Val.is_equal_sat ~get_type:(type_checker astate) ~revisited_allocs:astate.revisited_allocs


let is_equal_valid astate =
  Val.is_equal_valid ~get_type:(type_checker astate) ~revisited_allocs:astate.revisited_allocs


let is_inequal_sat astate =
  Val.is_inequal_sat ~get_type:(type_checker astate) ~revisited_allocs:astate.revisited_allocs


let is_inequal_valid astate =
  Val.is_inequal_valid ~get_type:(type_checker astate) ~revisited_allocs:astate.revisited_allocs


(** Eval functions *)
let eval_binop astate binop vals1 vals2 =
  let eval_binop_float v1 v2 =
    (* TODO: * Mult or Div: should we split state whether v2 is zero?  *)
    match binop with
    | Binop.PlusA _ | Binop.MinusA _ ->
        Val.join_float v1 v2
    | Binop.Div when is_equal_valid astate v2 Val.zero ->
        Val.VFloat FNaN
    | Binop.Div ->
        Val.top_primitive
    | Binop.Mult _ ->
        Val.join_float v1 v2
    | _ ->
        L.(die InternalError) "Not a float op"
  in
  let eval_binop_symval v1 v2 =
    match binop with
    | Binop.PlusA None | Binop.MinusA None | Binop.Mult None ->
        eval_binop_float v1 v2
    | Binop.PlusA _ ->
        let value = Val.add v1 v2 in
        astate.vtmap <- VTMap.weak_update value AbsTyp.int astate.vtmap ;
        value
    | Binop.MinusA _ ->
        let value = Val.sub v1 v2 in
        astate.vtmap <- VTMap.weak_update value AbsTyp.int astate.vtmap ;
        value
    | Binop.Mult _ when List.exists (equal_values astate v2) ~f:(Val.equal Val.zero) ->
        Val.zero
    | Binop.Mult _ when List.exists (equal_values astate v1) ~f:(Val.equal Val.zero) ->
        Val.zero
    | Binop.Mult _
      when List.exists (inequal_values astate v2) ~f:(Val.equal Val.zero)
           && List.exists (inequal_values astate v1) ~f:(Val.equal Val.zero) ->
        let value = Val.make_commut_inj Models.mult v1 v2 in
        astate.vtmap <- VTMap.weak_update value AbsTyp.int astate.vtmap ;
        value
    | Binop.BAnd when Val.is_true v1 && Val.is_true v2 ->
        Val.one
    | Binop.BAnd when Val.is_false v1 || Val.is_false v2 ->
        Val.zero
    | Binop.BOr when Val.is_true v1 || Val.is_true v2 ->
        Val.one
    | Binop.BOr when Val.is_false v1 && Val.is_false v2 ->
        Val.zero
    | Binop.BXor when (Val.is_true v1 && Val.is_true v2) || (Val.is_false v1 && Val.is_false v2) ->
        Val.one
    | Binop.BXor when (Val.is_true v1 && Val.is_false v2) || (Val.is_false v1 && Val.is_true v2) ->
        Val.zero
    | _ ->
        Val.top_primitive
  in
  AbsVal.fold
    (fun v1 -> AbsVal.fold (fun v2 -> AbsVal.add (eval_binop_symval v1 v2)) vals2)
    vals1 AbsVal.empty


let eval_unop astate unop vals =
  match unop with
  | Unop.Neg ->
      AbsVal.map
        (fun v ->
          let abstyp = read_typ astate v in
          if AbsTyp.check_instance ~lhs:abstyp ~rhs:AbsTyp.float |> is_yes then Val.minus_float v
          else
            let value = Val.make_injective Models.minus [v] in
            astate.vtmap <- VTMap.weak_update value AbsTyp.int astate.vtmap ;
            value )
        vals
  | Unop.BNot ->
      (* DECISION: not support *)
      AbsVal.top_primitive
  | Unop.LNot ->
      (* DECISION: do it in prune instr *)
      AbsVal.top_primitive


let true_value astate node = make_const astate node Val.one

let false_value astate node = make_const astate node Val.zero

let read_id astate id =
  match astate.last_org with
  | Original ->
      (Reg.find id astate.reg, IdUse.find id astate.id_use |> SymDiff.of_uses)
  | Current _ when Reg.mem id astate.reg ->
      (Reg.find id astate.reg, SymDiff.diff)
  | Current (_, org_state) ->
      (* TODO: should we compute uses? *)
      (* (Reg.find id org_state.reg, IdUse.find id astate.id_use |> SymDiff.of_uses) *)
      (Reg.find id org_state.reg, SymDiff.empty)
  | Past _ when Reg.mem id astate.reg ->
      (Reg.find id astate.reg, SymDiff.diff)
  | Past (_, org_state) ->
      (Reg.find id org_state.reg, SymDiff.diff)


let rec eval astate node instr exp : DiffVal.t =
  let instr_node = Node.of_pnode node instr in
  match exp with
  (* | Exp.Cast (typ, hole) when Fault.is_hole hole && Typ.equal Typ.pointer_to_java_lang_string typ ->
      (AbsVal.top, Disjunct.empty) *)
  | Exp.Cast (typ, hole) when Fault.is_hole hole ->
      (* FL4APR: evaluate hole expression *)
      (make_hole astate instr_node ~typ |> AbsVal.singleton, SymDiff.diff)
  | Exp.Var id ->
      read_id astate id
  | Exp.UnOp (unop, e, _) ->
      let v, symdiff = eval astate node instr e in
      (eval_unop astate unop v, symdiff)
  | Exp.BinOp (binop, e1, e2) ->
      let v1, symdiff1 = eval astate node instr e1 in
      let v2, symdiff2 = eval astate node instr e2 in
      (eval_binop astate binop v1 v2, SymDiff.join symdiff1 symdiff2)
  | Exp.Exn e ->
      eval astate node instr e
  | Exp.Const (Cstr str) ->
      (make_const astate instr_node (Val.make_string str) |> AbsVal.singleton, SymDiff.empty)
  | Exp.Const (Cint intlit) when IntLit.isnull intlit ->
      (make_const astate instr_node Val.null |> AbsVal.singleton, SymDiff.empty)
  | Exp.Const (Cint intlit) ->
      (make_const astate instr_node (Val.make_int intlit) |> AbsVal.singleton, SymDiff.empty)
  | Exp.Const (Cfloat flit) ->
      (make_const astate instr_node (Val.make_float flit) |> AbsVal.singleton, SymDiff.empty)
  | Exp.Const (Cclass name) ->
      let class_name = Ident.name_to_string name in
      let class_value =
        Val.make_injective Models.cls [Val.make_string class_name |> make_const astate instr_node]
      in
      let class_typ = AbsTyp.typ_from_string "java.lang.Class" in
      let abstyp = AbsTyp.make_instance class_typ in
      astate.vtmap <- VTMap.weak_update class_value abstyp astate.vtmap ;
      (AbsVal.singleton class_value, SymDiff.empty)
  | Exp.Cast (_, e) ->
      (* TODO: class cast exception or refine type *)
      eval astate node instr e
  | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ | Exp.Closure _ | Exp.Const (Cfun _) ->
      L.(die InternalError) "%a is not allowed as rvalue in java" Exp.pp exp
  | Exp.Sizeof _ ->
      (AbsVal.top_primitive, SymDiff.empty)


let eval astate node instr exp : DiffVal.t =
  let v, symdiff = eval astate node instr exp in
  match astate.last_org with Past _ -> (v, SymDiff.diff) | _ -> (v, symdiff)


let rec eval_lv astate node instr exp : Loc.Set.t * SymDiff.t =
  match exp with
  | Exp.Var id ->
      let v, symdiff = read_id astate id in
      (Loc.from_vals v, symdiff)
  | Exp.Const (Cstr _) ->
      let vals, _ = eval astate node instr exp in
      (Loc.from_vals vals, SymDiff.empty)
  | Exp.Cast (_, e) ->
      (* TODO: class cast exception or refine type *)
      eval_lv astate node instr e
  | Exp.Lindex (e1, e2) ->
      let locs, symdiff1 = eval_lv astate node instr e1 in
      let _, symdiff2 = eval astate node instr e2 in
      (Loc.append_indexs locs, SymDiff.join symdiff1 symdiff2)
  | Exp.Lvar pv ->
      (Loc.of_pvar pv |> Loc.Set.singleton, SymDiff.empty)
  | Exp.Lfield (e, fn, _) ->
      let locs, symdiff = eval_lv astate node instr e in
      (Loc.append_fields ~fn locs, symdiff)
  | Exp.Const (Cclass _) ->
      let vals, _ = eval astate node instr exp in
      (Loc.from_vals vals, SymDiff.empty)
  | _ ->
      L.(die InternalError) "%a is not allowed as lvalue expression in java" Exp.pp exp


let eval_lv astate node instr exp : Loc.Set.t * SymDiff.t =
  let locs, symdiff = eval_lv astate node instr exp in
  match astate.last_org with Past _ -> (locs, SymDiff.diff) | _ -> (locs, symdiff)


let eval_opt astate node instr exp_opt =
  match exp_opt with
  | None when has_past_original astate ->
      (AbsVal.bottom, SymDiff.diff)
  | None ->
      (AbsVal.bottom, SymDiff.empty)
  | Some exp ->
      eval astate node instr exp


(** remove unreachable * For top-down analysis (entry-site), maintain only callee-relative state to
    avoid multiple states with different caller memory, but same callee memory. 1. reachable locs of
    formal parameter after interproc assignments. 2. reachable locs of static fields

    * For bottom-up analysis (return-site), maintain only symbolic states to join states with
    different local memory, but same symbolic memory. 1. reachable values of symboilc memory 2.
    reachable values of return variable

    * At call-ret-site, maintain only caller-relative states. 1. reachable locs of static fields 2.
    reachable locs of caller variables after interproc assignments or summary instantiation 3.
    (bottom-up) reachable values of symbolic memory *)
module LocTable = WeakMap.Make (Loc) (Loc.Set)

let compute_field_map memory =
  Mem.fold
    (fun l _ acc ->
      match l with
      | Loc.Field _ | Loc.Index _ ->
          LocTable.weak_update (Loc.base_of l) (Loc.Set.singleton l) acc
      | _ ->
          acc )
    memory LocTable.empty


let compute_reachables_locs_from astate field_map locs =
  (* return, variables, global, symbol *)
  let visited = ref Loc.Set.empty in
  let rec __locs_reachable_from worklist acc =
    match worklist with
    | [] ->
        acc
    | work :: rest when Loc.Set.mem work !visited ->
        __locs_reachable_from rest acc
    | work :: rest ->
        visited := Loc.Set.add work !visited ;
        let field_reachable = Loc.Set.add work (LocTable.find work field_map) in
        let points_to_reachable =
          (* NOTE: read_locs executes join, so it could generate top instead of union of values *)
          Loc.Set.fold
            (fun l acc ->
              match read_loc_opt astate l with
              | Some value ->
                  Loc.from_vals value |> Loc.Set.union acc
              | None ->
                  acc )
            field_reachable Loc.Set.empty
        in
        let new_reachable = Loc.Set.union field_reachable points_to_reachable in
        __locs_reachable_from
          (Loc.Set.elements points_to_reachable @ rest)
          (Loc.Set.union acc new_reachable)
  in
  let reachables = __locs_reachable_from (Loc.Set.elements locs) locs in
  reachables


let compute_reachability_from_base astate ~base_locs ~base_vals =
  let astate = astate_with_merged_mem astate in
  let locs = Loc.Set.union base_locs (Loc.from_vals base_vals) in
  let field_map = compute_field_map astate.mem in
  let reachable_locs = compute_reachables_locs_from astate field_map locs in
  (* TODO: remove unreachable states from locs (memory, pathcond, ...) *)
  let reachable_vals =
    Mem.fold
      (fun l vals acc -> if Loc.Set.mem l reachable_locs then AbsVal.union vals acc else acc)
      astate.mem AbsVal.empty
    |> AbsVal.union base_vals
  in
  (* L.progress " - base locs: %a@." Loc.Set.pp base_locs ;
     L.progress " - field_map: %a@." LocTable.pp field_map ;
     L.progress " - locs: %a@." Loc.Set.pp locs ;
     L.progress " - base vals: %a@." AbsVal.pp base_vals ;
     L.progress " - reachable locs: %a@." Loc.Set.pp reachable_locs ;
     L.progress " - reachable vals: %a@." AbsVal.pp reachable_vals ; *)
  (reachable_locs, reachable_vals)


let remove_unreachables astate ~reachable_locs ~reachable_vals =
  let reachable_nodes =
    AbsVal.fold
      (fun v acc -> match v with VHeap n -> Node.Set.add n acc | _ -> acc)
      reachable_vals Node.Set.empty
  in
  let is_reachable_loc l = Loc.Set.mem l reachable_locs in
  let is_reachable_value v = AbsVal.mem v reachable_vals in
  let trackable_values =
    LocUse.fold
      (fun l d acc -> if is_reachable_loc l then Disjunct.to_vals d |> AbsVal.union acc else acc)
      astate.loc_use reachable_vals
    |> AbsVal.union (Changed.get_values astate.changed)
  in
  let is_trackable_value v = AbsVal.mem v trackable_values in
  let reg = Reg.empty in
  let mem = Mem.filter (fun l _ -> is_reachable_loc l) astate.mem in
  let pc = PC.filter_by_value ~f:is_reachable_value astate.pc in
  let vtmap = VTMap.filter (fun v _ -> is_trackable_value v) astate.vtmap in
  let visited_allocs =
    Node.Set.filter (fun n -> Node.Set.mem n reachable_nodes) astate.visited_allocs
  in
  let revisited_allocs =
    Node.Set.filter (fun n -> Node.Set.mem n reachable_nodes) astate.revisited_allocs
  in
  let replaced_values = astate.replaced_values in
  let invalidated_values = (* no values to remove: invalid symbols *) astate.invalidated_values in
  let assert_conds = (* no values to remove: symbol = symbol or constant *) astate.assert_conds in
  let loc_def = LocDef.filter (fun l _ -> is_reachable_loc l) astate.loc_def in
  let loc_use = LocUse.filter (fun l _ -> is_reachable_loc l) astate.loc_use in
  let last_org =
    match astate.last_org with
    | Past (node, ostate) ->
        let reg = Reg.empty in
        let mem = Mem.filter (fun l _ -> is_reachable_loc l) ostate.mem in
        let loc_use = LocUse.filter (fun l _ -> is_reachable_loc l) ostate.loc_use in
        let loc_def = LocDef.filter (fun l _ -> is_reachable_loc l) ostate.loc_def in
        Past (node, {ostate with reg; mem; loc_use; loc_def})
    | _ ->
        astate.last_org
  in
  update_state astate ~reg ~pc ~mem ~vtmap ~invalidated_values ~replaced_values ~assert_conds
    ~visited_allocs ~revisited_allocs ~loc_def ~loc_use ~last_org


let remove_unreachables_summary astate proc_desc : t =
  let formal_pvars = Procdesc.get_pvar_formals proc_desc in
  let base_locs =
    let ret_loc = proc_desc |> Procdesc.get_ret_var |> Loc.of_pvar in
    Mem.fold
      (fun l _ acc ->
        match l with Loc.Field (SymHeap (Val.VSymbol _), _) -> Loc.Set.add l acc | _ -> acc )
      astate.mem (Loc.Set.singleton ret_loc)
  in
  let formal_vals =
    List.mapi ~f:(fun i (pv, _) -> Val.VSymbol (Symbol.of_pvar i pv)) formal_pvars |> AbsVal.of_list
  in
  let base_vals =
    AbsVal.filter (function VSymbol s -> Symbol.is_param s | _ -> false) (all_values astate)
    |> AbsVal.union formal_vals
  in
  let reachable_locs, reachable_vals =
    compute_reachability_from_base astate ~base_locs ~base_vals
  in
  remove_unreachables astate ~reachable_locs ~reachable_vals


(** For Join *)
module Feature = struct
  type t =
    { is_exceptional: bool
    ; is_conditional: bool
    ; is_original: bool
    ; last_org_node: Node.t
    ; is_fault_empty: bool
    ; important_type: AbsTyp.t list
    ; return_type: AbsTyp.t option }
  [@@deriving compare]

  let pp fmt x =
    (* TODO: do it *)
    F.fprintf fmt "%b:%b" x.is_exceptional x.is_original
end

module FeatureMap = PrettyPrintable.MakePPMap (Feature)

let join_reg lhs rhs =
  if phys_equal lhs.reg rhs.reg then lhs.reg
  else
    let v_none id org_state_opt =
      match org_state_opt with Some org_state -> Reg.find id org_state.reg | None -> AbsVal.bottom
    in
    let org_state_opt =
      match lhs.last_org with
      | Original ->
          None
      | Past (_, org_state) | Current (_, org_state) ->
          Some org_state
    in
    Reg.merge
      (fun id v_lhs_opt v_rhs_opt ->
        match (v_lhs_opt, v_rhs_opt) with
        | Some v_lhs, Some v_rhs ->
            Some (AbsVal.join v_lhs v_rhs)
        | Some v_lhs, None ->
            Some (AbsVal.join v_lhs (v_none id org_state_opt))
        | None, Some v_rhs ->
            Some (AbsVal.join v_rhs (v_none id org_state_opt))
        | None, None ->
            None )
      lhs.reg rhs.reg


let join_mem lhs rhs =
  if phys_equal lhs.mem rhs.mem then lhs.mem
  else
    let is_constructor = Procname.is_constructor lhs.current_proc in
    let v_none l org_state_opt =
      match (Loc.to_symbol_opt l, org_state_opt) with
      | Some Symbol.(Path (Param _, _)), _ when is_constructor ->
          (* use uninitialized value, TODO: update primitive *)
          AbsVal.singleton Val.VNull
      | Some s, _ ->
          AbsVal.singleton (Val.VSymbol s)
      | None, _ ->
          AbsVal.bottom
    in
    let org_state_opt =
      match lhs.last_org with
      | Original ->
          None
      | Past (_, org_state) | Current (_, org_state) ->
          Some org_state
    in
    Mem.merge
      (fun l v_lhs_opt v_rhs_opt ->
        match (v_lhs_opt, v_rhs_opt) with
        | Some v_lhs, Some v_rhs ->
            Some (AbsVal.join v_lhs v_rhs)
        | Some v_lhs, None ->
            (* use uninitialized value, TODO: update primitive *)
            Some (AbsVal.join v_lhs (v_none l org_state_opt))
        | None, Some v_rhs ->
            Some (AbsVal.join v_rhs (v_none l org_state_opt))
        | None, None ->
            None )
      lhs.mem rhs.mem


let is_defined_loc astate (l, def, v) =
  if Node.ASet.equal def (LocDef.find l astate.loc_def) then true
  else
    match read_loc_opt astate l with
    | Some v' -> (
      match (AbsVal.is_singleton_or_more v, AbsVal.is_singleton_or_more v') with
      | Singleton v, Singleton v' when Val.equal v v' ->
          not (Val.is_abstract v)
      | _ ->
          false )
    | None ->
        false


let join lhs rhs =
  if phys_equal lhs rhs then (
    L.d_printfln "Two state are pyhsical equal" ;
    lhs )
  else
    { reg= join_reg lhs rhs
    ; mem= join_mem lhs rhs
    ; pc= PC.join lhs.pc rhs.pc
    ; vtmap= VTMap.join ~lhs:lhs.vtmap ~rhs:rhs.vtmap
    ; visited_allocs= Node.Set.union lhs.visited_allocs rhs.visited_allocs
    ; revisited_allocs= Node.Set.union lhs.revisited_allocs rhs.revisited_allocs
    ; replaced_values= ReplacedValMap.join lhs.replaced_values rhs.replaced_values
    ; invalidated_values= AbsVal.inter lhs.invalidated_values rhs.invalidated_values
    ; assert_conds= AssertConds.inter lhs.assert_conds rhs.assert_conds
    ; is_exceptional= lhs.is_exceptional
    ; is_conditional= lhs.is_conditional
    ; is_incomplete= lhs.is_incomplete || rhs.is_incomplete
    ; changed= Changed.join lhs.changed rhs.changed
    ; last_org= lhs.last_org
    ; id_use= IdUse.join lhs.id_use rhs.id_use
    ; loc_use= LocUse.join lhs.loc_use rhs.loc_use
    ; loc_def= LocDef.join lhs.loc_def rhs.loc_def
    ; abs_patches= AbsFault.join lhs.abs_patches rhs.abs_patches
    ; current_proc= lhs.current_proc
    ; current_ctxs= lhs.current_ctxs
    ; control_deps= ControlDeps.join lhs.control_deps rhs.control_deps
    ; important_param= lhs.important_param }


let is_equal_exception lhs rhs =
  if is_exceptional lhs then
    let ret_loc =
      Program.pdesc_of (Program.from_marshal ()) lhs.current_proc
      |> Procdesc.get_ret_var |> Loc.of_pvar
    in
    let lhs_val, _ = read_loc lhs (ret_loc, SymDiff.empty) in
    let rhs_val, _ = read_loc rhs (ret_loc, SymDiff.empty) in
    let lhs_typ, rhs_typ = (read_typ_of_vals lhs lhs_val, read_typ_of_vals rhs rhs_val) in
    AbsTyp.is_different (Some lhs_typ) (Some rhs_typ) |> not
  else true


let joinable lhs rhs =
  let debug_if_true msg b =
    L.d_printfln "@.%a and %a joinable on %s:@." pp_sig lhs pp_sig rhs msg ;
    b
  in
  (* TODO: check this is efficient *)
  match (lhs.last_org, rhs.last_org) with
  | _ when phys_equal lhs rhs ->
      L.d_printfln "@.%a and %a joinable on phys_equal@." pp_sig lhs pp_sig lhs ;
      true
  | _ when is_exceptional lhs ->
      true
  | _ when lhs.is_conditional && rhs.is_conditional ->
      AbsFault.equal lhs.abs_patches rhs.abs_patches
  | Original, Original ->
      true
  | _ when not (Changed.is_empty lhs.changed) ->
      (* Other heuristics cands: (Changed.equal lhs.changed rhs.changed  *)
      if is_exceptional lhs then true
      else
        (Changed.subset lhs.changed rhs.changed || Changed.subset rhs.changed lhs.changed)
        |> debug_if_true "changed subset"
        || Mem.equal lhs.mem rhs.mem |> debug_if_true "changed equal on mem"
  | _ when Config.sprint_exnchecker ->
      true
  | _ when AbsFault.equal lhs.abs_patches rhs.abs_patches ->
      L.d_printfln "@.%a and %a joinable on equal abs_patches@." pp_sig lhs pp_sig lhs ;
      AssertConds.equal lhs.assert_conds rhs.assert_conds
  | _ ->
      Reg.equal AbsVal.equal lhs.reg rhs.reg
      && Mem.equal lhs.mem rhs.mem
      && AssertConds.equal lhs.assert_conds rhs.assert_conds |> debug_if_true "reg, mem, assert"


module IntSet = AbstractDomain.FiniteSet (Int)
module IntSetMap = WeakMap.Make (IntSet) (Contexts)
module CtxIntSetMap = WeakMap.Make (Context) (IntSet)

let partition_contexts disjuncts =
  let contexts_partition =
    let context_i_map =
      List.foldi disjuncts ~init:CtxIntSetMap.empty ~f:(fun i acc astate ->
          Contexts.fold
            (fun ctx -> CtxIntSetMap.weak_update ctx (IntSet.singleton i))
            astate.current_ctxs acc )
    in
    CtxIntSetMap.fold
      (fun ctx set -> IntSetMap.weak_update set (Contexts.singleton ctx))
      context_i_map IntSetMap.empty
  in
  IntSetMap.fold
    (fun iset ctxs acc ->
      let disjuncts =
        List.filter_mapi disjuncts ~f:(fun i astate ->
            if IntSet.mem i iset then Some (set_ctx astate ctxs) else None )
      in
      disjuncts :: acc )
    contexts_partition []


let partition_by_feature disjuncts =
  let add_state (feature_map : t list FeatureMap.t) (state : t) =
    let last_org_node =
      match state.last_org with
      | Original ->
          Node.dummy
      | Current _ ->
          Node.dummy
      | Past _ when Config.sprint_exnchecker ->
          Node.dummy
      | Past (_, _) ->
          Node.dummy_of "FL4APR_Past"
    in
    let symbol_types =
      match VTMap.find_opt (Val.make_hole Node.dummy) state.vtmap with
      | Some abstyp ->
          [abstyp]
      | None ->
          []
    in
    let feature =
      Feature.
        { is_exceptional= state.is_exceptional
        ; is_conditional= state.is_conditional
        ; is_original= is_original state
        ; last_org_node
        ; is_fault_empty= AbsFault.is_original state.abs_patches
        ; important_type= get_important_type state @ symbol_types
        ; return_type= get_return_type state }
    in
    match FeatureMap.find_opt feature feature_map with
    | Some states ->
        FeatureMap.add feature (state :: states) feature_map
    | None ->
        FeatureMap.add feature [state] feature_map
  in
  let feature_map = List.fold disjuncts ~init:FeatureMap.empty ~f:add_state in
  FeatureMap.fold (fun _ disjuncts acc -> disjuncts :: acc) feature_map []


let merge_single_contexts disjuncts =
  let rec _merge worklist acc =
    match worklist with
    | [] ->
        acc
    | hd :: tl when Config.sprint_exnchecker ->
        let joinable, unjoinable = List.partition_tf tl ~f:(joinable hd) in
        if List.is_empty joinable then _merge tl (hd :: acc)
        else
          let joined = List.fold joinable ~init:hd ~f:join in
          _merge unjoinable (joined :: acc)
    | hd :: tl ->
        let joinable_by_abs_patches, unjoinable_by_abs_patches =
          if Option.is_some hd.abs_patches then
            List.partition_tf tl ~f:(fun astate -> AbsFault.equal hd.abs_patches astate.abs_patches)
          else ([], tl)
        in
        if not (List.is_empty joinable_by_abs_patches) then
          let joined = List.fold joinable_by_abs_patches ~init:hd ~f:join in
          _merge unjoinable_by_abs_patches (joined :: acc)
        else
          let joinable, unjoinable = List.partition_tf tl ~f:(joinable hd) in
          if List.is_empty joinable then _merge tl (hd :: acc)
          else
            let joined = List.fold joinable ~init:hd ~f:join in
            _merge unjoinable (joined :: acc)
  in
  let partitioned = partition_by_feature disjuncts in
  List.fold partitioned ~init:[] ~f:(fun acc disjuncts -> _merge disjuncts acc)


let merge disjuncts = List.concat_map (partition_contexts disjuncts) ~f:merge_single_contexts

(** logics to resolve control dependency *)
let resolve_conditional ~is_after node instr astate =
  match astate.abs_patches with
  | Some abs_patches when is_conditional astate -> (
    match Fault.Set.choose abs_patches with
    | {desc= ShouldSkip; loc= Range (_, After to_node)}
      when is_after && InstrNode.equal_except_vflag (Node.of_pnode node instr) to_node ->
        unset_conditional astate
    | {desc= ShouldSkip; loc= Range (_, Before to_node)}
      when (not is_after) && InstrNode.equal_except_vflag (Node.of_pnode node instr) to_node ->
        unset_conditional astate
    | {desc= MissingErrorHandling `Return}
      when Procdesc.Node.equal_nodekind (Procdesc.Node.get_kind node) Procdesc.Node.Exit_node ->
        unset_conditional astate
    | _ ->
        astate )
  | _ ->
      astate


let _resolve_control_deps astate ~old ~recent =
  let locs =
    Mem.fold (fun l _ -> Loc.Set.add l) old.mem Loc.Set.empty
    |> Mem.fold (fun l _ -> Loc.Set.add l) recent.mem
  in
  L.d_printfln "resolve control deps for %a" pp_sig astate ;
  Loc.Set.fold
    (fun l acc ->
      if Mem.mem l astate.mem then acc
      else if not (Mem.mem l recent.mem) then acc
      else
        let recent_def = LocDef.find l recent.loc_def in
        let old_def = LocDef.find l old.loc_def in
        if Node.ASet.equal recent_def old_def then acc
        else
          let _ =
            L.d_printfln " - %a is different from recent memory:@.   * %a@.   * %a)" Loc.pp l
              Node.ASet.pp old_def Node.ASet.pp recent_def
          in
          match read_loc_opt old l with
          | Some v ->
              let astate = store_loc Node.dummy l (v, SymDiff.diff) acc in
              {astate with loc_def= LocDef.add l recent_def astate.loc_def}
          | None ->
              acc )
    locs astate
  |> VTMap.fold
       (fun v abstyp acc ->
         if VTMap.mem v astate.vtmap then acc else store_typ (AbsVal.singleton v) abstyp acc )
       recent.vtmap


let resolve_control_deps_after_instr node instr astate ~original_post_opt =
  let astate = resolve_conditional ~is_after:true node instr astate in
  let instr_node = Node.of_pnode node instr in
  match (astate.last_org, original_post_opt) with
  | Original, _ ->
      astate
  | _ when astate.is_conditional ->
      astate
  | Current (node, old), None ->
      {astate with last_org= Past (node, old)}
  | Current _, Some recent ->
      {astate with last_org= Current (instr_node, recent)}
  | Past _, None ->
      astate
  | Past _, Some _ when Config.sprint_exnchecker || Config.sprint_no_test ->
      astate
  | Past (_, old), Some recent ->
      (* 1. if diff-state executed replaced_instr instead of original instr
         2. conditional state is unsetted *)
      let astate = _resolve_control_deps astate ~old ~recent in
      {astate with last_org= Current (instr_node, recent)}


let resolve_control_deps_before_instr node instr astate ~original_pre_opt =
  let astate = resolve_conditional ~is_after:false node instr astate in
  let instr_node = Node.of_pnode node instr in
  match (astate.last_org, original_pre_opt) with
  | Original, _ ->
      astate
  | _ when astate.is_conditional ->
      astate
  | Current (node, old), None ->
      (* original found to be fake (e.g., switch) *)
      {astate with last_org= Past (node, old)}
  | Current _, Some recent
    when Int.equal (VTMap.cardinal astate.vtmap) (VTMap.cardinal recent.vtmap) ->
      {astate with last_org= Current (instr_node, recent)}
  | Current _, Some recent ->
      let vtmap =
        VTMap.fold
          (fun v abstyp acc ->
            if VTMap.mem v astate.vtmap then acc else VTMap.update ~is_weak:false v abstyp acc )
          recent.vtmap astate.vtmap
      in
      {astate with last_org= Current (instr_node, recent); vtmap}
  | Past _, None ->
      astate
  | Past _, Some _ when Config.sprint_exnchecker || Config.sprint_no_test ->
      astate
  | Past (_, old), Some recent ->
      (* 1. diff-state with non-org flow is joined here
         2. conditional state is unsetted *)
      let astate = _resolve_control_deps astate ~old ~recent in
      {astate with last_org= Current (instr_node, recent)}


(** Pruning heuristics **)

let filter_by_invalid_values ~invalid_values astate : t =
  if AbsVal.is_empty invalid_values then astate
  else
    let _ = L.d_printfln "prune_by_invalid_values: %a@." AbsVal.pp invalid_values in
    let value_filter v =
      List.for_all (Val.get_subvalues v) ~f:(fun v -> not (AbsVal.mem v invalid_values))
    in
    let pc = PC.filter_by_value ~f:value_filter astate.pc in
    let mem = Mem.filter_by_value ~f:value_filter astate.mem in
    let reg = Reg.map (AbsVal.filter value_filter) astate.reg in
    let vtmap = (* caller will see invalidated values *) astate.vtmap in
    let replaced_values = (* for future src *) astate.replaced_values in
    let invalidated_values = AbsVal.union invalid_values astate.invalidated_values in
    let assert_conds =
      AssertConds.map
        (fun (v1, v2, kind, node) ->
          (AbsVal.filter value_filter v1, AbsVal.filter value_filter v2, kind, node) )
        astate.assert_conds
    in
    let loc_use = LocUse.filter (fun l _ -> Loc.is_heap_pred ~pred:value_filter l) astate.loc_use in
    let loc_def = LocDef.filter (fun l _ -> Loc.is_heap_pred ~pred:value_filter l) astate.loc_def in
    let last_org =
      (* TODO: should we remove invalid values in original states? *) astate.last_org
    in
    update_state astate ~pc ~mem ~reg ~vtmap ~invalidated_values ~replaced_values ~assert_conds
      ~visited_allocs:astate.visited_allocs ~revisited_allocs:astate.revisited_allocs ~loc_use
      ~loc_def ~last_org


let _prune_by_invalid_values astate invalid_values =
  let strong_updatables = AbsVal.filter (is_strong_updatable_val astate) invalid_values in
  filter_by_invalid_values astate ~invalid_values:strong_updatables


let _prune_invalid astate binop vals1 vals2 : t list * AbsVal.t * AbsVal.t =
  match binop with
  | Binop.Eq ->
      let (vals1_sat, vals1_invalid), (vals2_sat, vals2_invalid) =
        ( AbsVal.partition (fun v1 -> AbsVal.exists (is_equal_sat astate v1) vals2) vals1
        , AbsVal.partition (fun v2 -> AbsVal.exists (is_equal_sat astate v2) vals1) vals2 )
      in
      let invalid_values = AbsVal.join vals1_invalid vals2_invalid in
      if AbsVal.is_empty vals1_sat || AbsVal.is_empty vals2_sat then ([], vals1_sat, vals2_sat)
      else ([_prune_by_invalid_values astate invalid_values], vals1_sat, vals2_sat)
  | Binop.Ne ->
      let (vals1_sat, vals1_invalid), (vals2_sat, vals2_invalid) =
        ( AbsVal.partition (fun v1 -> AbsVal.exists (is_inequal_sat astate v1) vals2) vals1
        , AbsVal.partition (fun v2 -> AbsVal.exists (is_inequal_sat astate v2) vals1) vals2 )
      in
      let invalid_values = AbsVal.join vals1_invalid vals2_invalid in
      if AbsVal.is_empty vals1_sat || AbsVal.is_empty vals2_sat then ([], vals1_sat, vals2_sat)
      else ([_prune_by_invalid_values astate invalid_values], vals1_sat, vals2_sat)
  | _ ->
      ([astate], vals1, vals2)


let check_dynamic_flow instr_node ~is_org_flow symdiff astate =
  match add_changed instr_node ~is_org_flow symdiff astate with
  | Some astate ->
      [astate]
  | None ->
      []


let prune_by_binop instr_node ~is_org_flow binop vals1 vals2 symdiff astate =
  let astates_pruned, vals1', vals2' =
    match add_changed instr_node ~is_org_flow symdiff astate with
    | Some astate when is_yes is_org_flow && not (SymDiff.is_diff symdiff) ->
        ([astate], vals1, vals2)
    | Some astate ->
        let astates_pruned, vals1', vals2' = _prune_invalid astate binop vals1 vals2 in
        if List.is_empty astates_pruned then
          L.d_printfln "prune_by_binop: invalid PC (%a %s %a)" AbsVal.pp vals1
            (Binop.str Pp.text binop) AbsVal.pp vals2 ;
        (astates_pruned, vals1', vals2')
    | None ->
        L.d_printfln "prune_by_binop: org_value with non_org_flow" ;
        ([], AbsVal.empty, AbsVal.empty)
  in
  match (AbsVal.get_val_opt vals1', AbsVal.get_val_opt vals2') with
  | _ when Config.sprint_exnchecker ->
      astates_pruned
  | Some v1, Some v2
    when Binop.equal Binop.Eq binop && (not (Val.is_abstract v1)) && not (Val.is_abstract v2) ->
      (* TODO: currently, we choose v1 if v1, v2 are both symbolic *)
      if Val.is_identifiable_symbol v1 || Val.is_identifiable_symbol v2 then (
        let pathcond = PathCond.make_binop binop v1 v2 in
        L.d_printfln "Generated path condition : %a" PathCond.pp pathcond ;
        astates_pruned )
      else if Val.is_symbolic v1 then
        List.map astates_pruned ~f:(replace_value ~src:v1 ~dst:v2)
        |> List.filter ~f:(not <<< is_invalid)
      else if Val.is_symbolic v2 then
        List.map astates_pruned ~f:(replace_value ~src:v2 ~dst:v1)
        |> List.filter ~f:(not <<< is_invalid)
      else astates_pruned
  | Some v1, Some v2 ->
      let pathcond = PathCond.make_binop binop v1 v2 in
      L.d_printfln "Generated path condition : %a" PathCond.pp pathcond ;
      astates_pruned
  | Some _, None ->
      (* TODO: if x = {l1, l2} but, l1 != null & l2 != null, then x != null *)
      astates_pruned
  | None, Some _ ->
      (* TODO: if x = {l1, l2} but, l1 != null & l2 != null, then x != null *)
      astates_pruned
  | None, None ->
      astates_pruned


let exec_assertion instr_node binop vals1 vals2 symdiff astate =
  let assert_cond = (vals1, vals2, binop, instr_node) in
  let passing_states =
    let is_org_flow = is_dynamic_normal astate instr_node in
    if is_no is_org_flow then
      set_assertion assert_cond astate
      |> prune_by_binop instr_node ~is_org_flow binop vals1 vals2 symdiff
    else prune_by_binop instr_node ~is_org_flow binop vals1 vals2 symdiff astate
  in
  let failing_states =
    let pdesc = Program.pdesc_of (Program.from_marshal ()) astate.current_proc in
    let is_org_flow = is_dynamic_throw astate instr_node in
    let disjuncts =
      match Binop.negate binop with
      | Some binop' when is_yes is_org_flow ->
          set_assertion assert_cond astate
          |> prune_by_binop instr_node ~is_org_flow binop' vals1 vals2 symdiff
      | Some binop' ->
          prune_by_binop instr_node ~is_org_flow binop' vals1 vals2 symdiff astate
      | None ->
          prune_by_binop instr_node ~is_org_flow Binop.Eq AbsVal.top_primitive AbsVal.top_primitive
            symdiff astate
    in
    List.map disjuncts
      ~f:
        (throw_err instr_node (Procdesc.get_ret_var pdesc)
           ~exn_typ_str:"org.junit.Assert.AssertionError" )
  in
  (* TODO: could assert-failed state be cathed? *)
  passing_states @ failing_states


let _prune_invalid_typ astate values abstyp ~is =
  let valid_values, sat_values, invalid_values =
    AbsVal.fold
      (fun v (valid_values, sat_values, invalid_values) ->
        match VTMap.find_opt v astate.vtmap with
        | Some abstyp' -> (
          match AbsTyp.check_equal (abstyp', abstyp) with
          | `Yes when is ->
              (AbsVal.set_add v valid_values, sat_values, invalid_values)
          | `No when is ->
              (valid_values, sat_values, AbsVal.set_add v invalid_values)
          | `Yes ->
              (valid_values, sat_values, AbsVal.set_add v invalid_values)
          | `No ->
              (AbsVal.set_add v valid_values, sat_values, invalid_values)
          | `Unknown ->
              (valid_values, AbsVal.set_add v sat_values, invalid_values) )
        | None ->
            (valid_values, AbsVal.set_add v sat_values, invalid_values) )
      values
      (AbsVal.empty, AbsVal.empty, AbsVal.empty)
  in
  if AbsVal.is_empty valid_values && AbsVal.is_empty sat_values then ([], valid_values, sat_values)
  else ([filter_by_invalid_values ~invalid_values astate], valid_values, sat_values)


let prune_by_typ astate values abstyp ~is =
  let astates, _, sat_values = _prune_invalid_typ astate ~is values abstyp in
  if is then List.map astates ~f:(store_typ sat_values abstyp)
  else (* TODO: design heuristics *) astates


let ret_is_undefined astate =
  let program = Program.from_marshal () in
  let proc = astate.current_proc in
  let ret_var = Procdesc.get_ret_var (Program.pdesc_of program proc) in
  let ret_loc = Loc.of_pvar ret_var in
  match astate.last_org with
  | _ when not (is_exceptional astate) ->
      false
  | Original ->
      not (Mem.mem ret_loc astate.mem)
  | Current (_, ostate) | Past (_, ostate) ->
      not (Mem.mem ret_loc astate.mem || Mem.mem ret_loc ostate.mem)


let is_normal_with_patches astate =
  (not (is_exceptional astate)) && not (AbsFault.is_original astate.abs_patches)
