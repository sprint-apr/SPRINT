open! IStd
open! Vocab
module F = Format
module L = Logging
open BasicDom

module Val = struct
  type t = {locs: PowLoc.t; procs: PowProc.t} [@@deriving compare]

  let equal = [%compare.equal: t]

  let leq ~lhs ~rhs =
    PowLoc.leq ~lhs:lhs.locs ~rhs:rhs.locs && PowProc.leq ~lhs:lhs.procs ~rhs:rhs.procs


  let bottom = {locs= PowLoc.empty; procs= PowProc.empty}

  let pp fmt {locs; procs} = F.fprintf fmt "(%a, %a)" PowLoc.pp locs PowProc.pp procs

  let join lhs rhs = {locs= PowLoc.join lhs.locs rhs.locs; procs= PowProc.join lhs.procs rhs.procs}

  let[@warning "-27"] widen ~prev ~next ~num_iters = join prev next

  let is_diff_simple v1 v2 = Int.equal (PowLoc.cardinal v1.locs) (PowLoc.cardinal v2.locs) |> not

  let is_bottom = equal bottom

  let of_locs locs = {bottom with locs}

  let of_procs procs = {bottom with procs}

  let rec default_of_typ ~is_exact ~ctx = function
    | Typ.{desc= Tstruct name} ->
        Some (Loc.of_class ~is_exact ~ctx name |> PowLoc.singleton |> of_locs)
    | Typ.{desc= Tarray {elt= t}} ->
        default_of_typ ~is_exact ~ctx t
    | Typ.{desc= Tptr (t, _)} ->
        default_of_typ ~is_exact ~ctx t
    | _ ->
        None


  let get_locs {locs} = locs

  let get_procs {procs} = procs

  let replace_locs v locs = {v with locs}
end

module Reg = struct
  include WeakMap.Make (Loc) (Val)

  let weak_update loc v mem = if Loc.is_null loc then mem else weak_update loc v mem
end

module Mem = struct
  include WeakMap.Make (Loc) (Val)

  let find l m =
    match l with
    | Loc.Field (Allocsite (ctx, a), fn) when Allocsite.is_abstract a -> (
      match Program.get_field_typ_opt fn with
      | Some Typ.{desc= Tstruct name} ->
          Val.join
            (Loc.of_class ~is_exact:false ~ctx name |> PowLoc.singleton |> Val.of_locs)
            (find l m)
      | Some Typ.{desc= Tptr (Typ.{desc= Tstruct name}, _)} ->
          Val.join
            (Loc.of_class ~is_exact:false ~ctx name |> PowLoc.singleton |> Val.of_locs)
            (find l m)
      | _ ->
          find l m )
    | Loc.Index (Allocsite (ctx, a)) ->
        Val.join (Loc.Allocsite (ctx, a) |> PowLoc.singleton |> Val.of_locs) (find l m)
    | _ ->
        find l m


  let find_mem_set locs mem = PowLoc.fold (fun loc -> Val.join (find loc mem)) locs Val.bottom

  let pure_weak_update l v m = weak_update l v m

  let weak_update loc v mem = if Loc.is_null loc then mem else weak_update loc v mem

  let weak_update_set locs v mem = PowLoc.fold (fun loc -> weak_update loc v) locs mem
end

module FlatTypDomain = AbstractDomain.Flat (struct
  include Typ

  let pp = pp_full Pp.text
end)

module Loc2Typ = struct
  module LocWithoutCtx = struct
    include Loc

    let compare = compare_without_ctx
  end

  include AbstractDomain.Map (LocWithoutCtx) (FlatTypDomain)

  let find_typ t loc =
    match (find_opt loc t, loc) with
    | Some typelm, _ ->
        AbsTyp.make_exact (Option.value_exn (FlatTypDomain.get typelm))
    | None, Loc.Allocsite (_, a) -> (
      try Option.value_exn (Allocsite.get_abstyp_opt a)
      with _ -> L.(die InternalError) "no type defined for %a@." Allocsite.pp a )
    | None, _ when Loc.is_null loc ->
        raise Caml.Not_found
    | None, _ ->
        L.user_warning "Type of %a is not found!@." Loc.pp loc ;
        raise Caml.Not_found


  let add_typ t loc typ = add loc (FlatTypDomain.v typ) t
end

module Context = struct
  include BasicDom.Context

  let append program ctx node caller callee =
    let _ = callee in
    (* TODO: remove callee *)
    match ctx with
    | Empty testClass when Program.is_entry program caller ->
        Test (testClass, node)
    | _ ->
        ctx


  let empty_of = function Test (testClass, _) -> Empty testClass | ctx -> ctx
end

module Contexts = BasicDom.Contexts

type t = {reg: Reg.t; mem: Mem.t; mutable loc2typ: Loc2Typ.t}

let bottom = {reg= Reg.bottom; mem= Mem.bottom; loc2typ= Loc2Typ.empty}

let is_bottom = phys_equal bottom

let leq ~lhs ~rhs = Reg.leq ~lhs:lhs.reg ~rhs:rhs.reg && Mem.leq ~lhs:lhs.mem ~rhs:rhs.mem

let pp fmt {reg; mem; loc2typ} =
  F.fprintf fmt "REG: %a@. MEM: %a@. TENV: %a@." Reg.pp reg Mem.pp mem Loc2Typ.pp loc2typ


let type_of_loc {loc2typ} = Loc2Typ.find_typ loc2typ

let type_of_loc_opt t l = try Some (type_of_loc t l) with Caml.Not_found -> None

let weak_update_mem loc v t =
  if Loc.is_null loc then t else {t with mem= Mem.weak_update loc v t.mem}


let weak_update_mem_locs locs v t = PowLoc.fold (fun l -> weak_update_mem l v) locs t

let append_field ({loc2typ} as state) loc ~fn typ =
  let loc_field = Loc.append_field loc ~fn in
  state.loc2typ <- Loc2Typ.add_typ loc2typ loc_field typ ;
  loc_field


let append_fields state locs ~fn typ = PowLoc.map (fun loc -> append_field state loc ~fn typ) locs

let rec is_primitive_typ typ =
  match strip_ptr typ with
  | Typ.{desc= Tstruct name} ->
      is_primitive_wrapper name
  | Typ.{desc= Tarray {elt}} ->
      is_primitive_typ elt
  | _ ->
      false


let make_allocsite ctx node instr =
  let allocsite = Allocsite.of_pnode node instr in
  Loc.of_allocsite ~ctx allocsite


let type_of_field fld struct_typ =
  let lookup = Tenv.lookup (Program.tenv ()) in
  Struct.fld_typ ~lookup ~default:Typ.void_star fld struct_typ


let rec eval : Procname.t -> Context.t -> Exp.t -> t -> Val.t =
 fun pid ctx exp ({reg} as state) ->
  match exp with
  | Var id ->
      Reg.find (Loc.of_id ~ctx (id, pid)) reg
  | Lvar pv when Pvar.is_global pv ->
      Val.of_locs (PowLoc.singleton (Loc.of_pvar ~ctx:(Context.empty_of ctx) pv))
  | Lvar pv ->
      Val.of_locs (PowLoc.singleton (Loc.of_pvar ~ctx pv))
  | UnOp _ ->
      Val.bottom
  | BinOp (binop, e1, e2) ->
      eval_binop pid ctx binop e1 e2 state
  | Const c ->
      eval_const c
  | Cast (_, e) ->
      eval pid ctx e state
  | Lfield (e, fn, struct_typ) ->
      let basis = eval_locs pid ctx e state in
      let typ_fn = type_of_field fn struct_typ in
      Val.of_locs (PowLoc.map (fun loc -> append_field state ~fn loc typ_fn) basis)
  | Lindex (e1, _) ->
      Val.of_locs (PowLoc.map Loc.append_index (eval_locs pid ctx e1 state))
  | _ ->
      Val.bottom


and eval_const : Const.t -> Val.t = function
  | Cfun proc_name ->
      PowProc.singleton proc_name |> Val.of_procs
  | Cint intlit when IntLit.iszero intlit ->
      Val.of_locs PowLoc.null (* Null assign *)
  | Cint _ ->
      Val.bottom
  | _ ->
      Val.bottom


and eval_binop : Procname.t -> Context.t -> Binop.t -> Exp.t -> Exp.t -> t -> Val.t =
 fun pid ctx bop exp1 exp2 state ->
  match bop with
  | PlusPI when Exp.(is_null_literal exp2 || is_zero exp2) ->
      eval pid ctx exp1 state
  | MinusPI when Exp.(is_null_literal exp2 || is_zero exp2) ->
      eval pid ctx exp1 state
  | PlusPI | MinusPI ->
      let v1 = eval pid ctx exp1 state in
      let locs1 = Val.get_locs v1 in
      PowLoc.append_indexes locs1 |> PowLoc.union locs1 |> Val.replace_locs v1
  | _ ->
      Val.bottom


and eval_locs pid ctx exp state = Val.get_locs (eval pid ctx exp state)

and eval_procs pid ctx exp state = Val.get_procs (eval pid ctx exp state)

let locs_point_to {mem} loc =
  Mem.fold
    (fun l v acc -> if PowLoc.mem loc (Val.get_locs v) then PowLoc.add l acc else acc)
    mem PowLoc.empty


let ptsto_of_locs {mem} locs = Mem.find_mem_set locs mem |> Val.get_locs

let reachable_locs_of locs mem =
  let rec __reachable_locs_of worklist reachable_locs =
    if PowLoc.is_empty worklist then reachable_locs
    else
      let worklist = PowLoc.union_indexes worklist in
      let work = PowLoc.choose worklist in
      let rest = PowLoc.remove work worklist in
      let new_reachable_locs =
        let locs_point_to = locs_point_to mem work in
        let locs_field_detached =
          let rec detach l acc =
            if not (Loc.is_field l) then acc
            else
              let l' = Loc.detach_field l in
              detach l' (PowLoc.add l' acc)
          in
          detach work (PowLoc.singleton work)
        in
        PowLoc.diff (PowLoc.union locs_point_to locs_field_detached) reachable_locs
      in
      __reachable_locs_of
        (PowLoc.union rest new_reachable_locs)
        (PowLoc.union reachable_locs new_reachable_locs)
  in
  __reachable_locs_of locs locs


let weak_reachable_locs_of ?(depth = 2) locs mem =
  let __reachable_locs_of worklist =
    let worklist =
      worklist |> PowLoc.detach_fields |> PowLoc.detach_fields |> PowLoc.union_indexes
    in
    let reachable_locs =
      PowLoc.fold (fun l -> PowLoc.union (locs_point_to mem l)) worklist worklist
    in
    reachable_locs
  in
  if Int.equal depth 0 then locs
  else if Int.equal depth 1 then locs |> __reachable_locs_of
  else locs |> __reachable_locs_of |> __reachable_locs_of


let resolve_callees state pid ctx ~fexp ~this_exp instr loc =
  (* eval this_exp to get locs *)
  let locs = PowLoc.remove Loc.null (eval_locs pid ctx this_exp state) in
  let callees_before_dispatch = eval_procs pid ctx fexp state in
  let get_class_name typ =
    match strip_ptr typ with
    | Typ.{desc= Tstruct name} ->
        name
    | Typ.{desc= Tarray _} ->
        (* var args*)
        Typ.Name.Java.java_lang_object
    | _ ->
        L.(
          die InternalError "this evaluates non-class type  %a at %a(%a)" (Typ.pp_full Pp.text) typ
            pp_instr instr Location.pp_file_pos loc )
  in
  let accum_callee_procname loc acc =
    (* Gather all callee procname from loc *)
    match AbsTyp.typ_of (type_of_loc state loc) with
    | typ ->
        L.debug L.Analysis L.Verbose " - try to call by %a class from %a@." (Typ.pp_full Pp.text)
          typ Loc.pp loc ;
        let this_class = get_class_name typ in
        let replace pid =
          match Program.resolve_method this_class pid with Some callee -> callee | None -> pid
        in
        PowProc.union (PowProc.map replace callees_before_dispatch) acc
    | exception Caml.Not_found ->
        acc
  in
  (* Gather all callee procnames from all locs *)
  let callees = PowLoc.fold accum_callee_procname locs PowProc.empty in
  L.debug L.Analysis L.Verbose "CallInstr: %a (%a)@." pp_instr instr Location.pp_file_pos loc ;
  L.debug L.Analysis L.Verbose " - ThisExp: %a@." Exp.pp this_exp ;
  L.debug L.Analysis L.Verbose " - PowLocs of this_exp: %a@." PowLoc.pp locs ;
  L.debug L.Analysis L.Verbose " - Calles Before dispatch: %a@." PowProc.pp callees_before_dispatch ;
  L.debug L.Analysis L.Verbose " - Calles After dispatch: %a@." PowProc.pp callees ;
  callees


(** compute reachable memory from the given pid and locations *)
module LocTable = WeakMap.Make (Loc) (PowLoc)

let field_map = ref None

let compute_field_map memory =
  let collect_fields locs acc =
    PowLoc.fold (fun l -> LocTable.weak_update (Loc.base_of l) (PowLoc.singleton l)) locs acc
  in
  let map =
    Mem.fold (fun l v -> collect_fields (PowLoc.add l (Val.get_locs v))) memory LocTable.empty
  in
  field_map := Some map ;
  map


let locs_reachable_from ?(exclude_null = false) {mem} locs =
  let field_map =
    if Option.is_some !field_map then Option.value_exn !field_map else compute_field_map mem
  in
  let rec __locs_reachable_from worklist acc =
    if PowLoc.is_empty worklist then acc
    else
      let work = PowLoc.choose worklist in
      let rest = PowLoc.remove work worklist in
      let field_reachable = LocTable.find work field_map in
      let points_to_reachable = Val.get_locs (Mem.find_mem_set field_reachable mem) in
      let new_reachable = PowLoc.diff (PowLoc.union field_reachable points_to_reachable) acc in
      __locs_reachable_from (PowLoc.union rest new_reachable) (PowLoc.union acc new_reachable)
  in
  let reachables = __locs_reachable_from locs locs in
  if exclude_null then PowLoc.diff reachables PowLoc.null else reachables


let insensitive_memory astate =
  let reg_insen =
    Reg.fold
      (fun l v acc ->
        Reg.weak_update (Loc.empty_ctx_of l)
          (Val.replace_locs v (PowLoc.map Loc.empty_ctx_of (Val.get_locs v)))
          acc )
      astate.reg Reg.empty
  in
  let mem_insen =
    Mem.fold
      (fun l v acc ->
        Mem.pure_weak_update (Loc.empty_ctx_of l)
          (Val.replace_locs v (PowLoc.map Loc.empty_ctx_of (Val.get_locs v)))
          acc )
      astate.mem Mem.empty
  in
  {astate with reg= reg_insen; mem= mem_insen}
