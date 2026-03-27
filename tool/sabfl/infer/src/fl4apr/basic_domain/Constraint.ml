open! IStd
open! Vocab
open BasicDom
open BasicDom.Result
module F = Format
module L = Logging

module type S = sig
  include PrettyPrintable.PrintableEquatableOrderedType

  val zero : t

  val is_abstract : t -> bool (* v1 == v1 is even not valid. they are abstracted values *)

  val is_concrete : t -> bool (* v1 == v2 is invalid statement for any different value v1, v2 *)

  val check_equal : t -> t -> result

  val check_leq : t -> t -> result

  val replace_sub : t -> src:t -> dst:t -> t

  val replace_by_map : t -> f:(t -> t) -> t
end

module Make (Val : S) = struct
  type t =
    | BinComPred of (Procname.t * Val.t * Val.t)
    | Pred of (Procname.t * Val.t list)
    | Not of t
  [@@deriving compare]

  let rec sorted = function
    | BinComPred (f, v1, v2) when Val.is_concrete v1 ->
        BinComPred (f, v2, v1)
    | BinComPred (f, v1, v2) when Val.is_concrete v2 ->
        BinComPred (f, v1, v2)
    | BinComPred (f, v1, v2) when Val.compare v1 v2 <= 0 ->
        BinComPred (f, v1, v2)
    | BinComPred (f, v1, v2) ->
        BinComPred (f, v2, v1)
    | Pred _ as x ->
        x
    | Not x ->
        Not (sorted x)


  let compare x y = compare (sorted x) (sorted y)

  let equal = [%compare.equal: t]

  let rec pp fmt = function
    | BinComPred (f, v1, v2) ->
        F.fprintf fmt "%a %s %a" Val.pp v1 (Procname.get_method f) Val.pp v2
    | Pred (f, args) ->
        F.fprintf fmt "%s(%a)" (Procname.get_method f) (Pp.seq Val.pp ~sep:",") args
    | Not pc ->
        F.fprintf fmt "NOT(%a)" pp pc


  let rec replace_value x ~src ~dst =
    let result =
      match x with
      | BinComPred (f, v1, v2) ->
          BinComPred (f, Val.replace_sub v1 ~src ~dst, Val.replace_sub v2 ~src ~dst)
      | Not x ->
          Not (replace_value x ~src ~dst)
      | Pred (f, args) ->
          Pred (f, List.map args ~f:(Val.replace_sub ~src ~dst))
    in
    sorted result


  let rec replace_by_map ~map x =
    let result =
      match x with
      | BinComPred (f, v1, v2) ->
          BinComPred (f, Val.replace_by_map ~f:map v1, Val.replace_by_map ~f:map v2)
      | Not x ->
          Not (replace_by_map ~map x)
      | Pred (f, args) ->
          Pred (f, List.map args ~f:(Val.replace_by_map ~f:map))
    in
    sorted result


  let true_cond = BinComPred (Models.eq, Val.zero, Val.zero) (* top *)

  let false_cond = Not true_cond

  let is_true = equal true_cond

  let is_false = equal false_cond

  let rec check = function
    | BinComPred (f, v1, v2) when Procname.equal f Models.eq ->
        Val.check_equal v1 v2
    | BinComPred (f, v1, v2) when Procname.equal f Models.ne ->
        Val.check_equal v1 v2 |> Result.negate_result
    | Pred (f, [v1; v2]) when Procname.equal f Models.lt ->
        Result.conjunct (Val.check_leq v1 v2) (Val.check_equal v1 v2 |> Result.negate_result)
    | Pred (f, [v1; v2]) when Procname.equal f Models.leq ->
        Val.check_leq v1 v2
    | Pred (f, [v1; v2]) when Procname.equal f Models.gt ->
        Result.conjunct (Val.check_leq v2 v1) (Val.check_equal v2 v1 |> Result.negate_result)
    | Pred (f, [v1; v2]) when Procname.equal f Models.geq ->
        Val.check_leq v2 v1
    | Not x ->
        check x |> Result.negate_result
    | _ ->
        Result.Unknown


  let is_valid x = match check x with Valid -> true | _ -> false

  let is_invalid x = match check x with UnSAT -> true | _ -> false

  let rec contains_with_pred ~f = function
    | BinComPred (_, v1, v2) ->
        f v1 || f v2
    | Pred (_, args) ->
        List.exists args ~f
    | Not x ->
        contains_with_pred ~f x


  let contains_absval = contains_with_pred ~f:Val.is_abstract

  let is_trivial x = contains_absval x || is_valid x

  let make_negation = function Not x -> x | _ as x -> Not x

  let normalize = function
    | BinComPred (f, v1, v2) when Procname.equal Models.ne f ->
        Not (BinComPred (Models.eq, v1, v2))
    | Pred (f, [v1; v2]) when Procname.equal Models.gt f ->
        Pred (Models.lt, [v2; v1])
    | Pred (f, [v1; v2]) when Procname.equal Models.geq f ->
        Pred (Models.leq, [v2; v1])
    | Not (BinComPred (f, v1, v2)) when Procname.equal Models.ne f ->
        BinComPred (Models.eq, v1, v2)
    | Not (Pred (f, [v1; v2])) when Procname.equal Models.gt f ->
        (* not (v1 > v2) <=> v1 <= v2 *)
        Pred (Models.leq, [v1; v2])
    | Not (Pred (f, [v1; v2])) when Procname.equal Models.geq f ->
        (* not (v1 >= v2) <=> v1 < v2 *)
        Pred (Models.lt, [v1; v2])
    | Not (Pred (f, [v1; v2])) when Procname.equal Models.lt f ->
        (* not (v1 < v2) <=> v2 <= v1 *)
        Pred (Models.leq, [v2; v1])
    | Not (Pred (f, [v1; v2])) when Procname.equal Models.leq f ->
        (* not (v1 <= v2) <=> v2 < v1 *)
        Pred (Models.lt, [v2; v1])
    | _ as x ->
        x


  let make_binop binop v1 v2 =
    match binop with
    | Binop.Eq | Binop.Ne ->
        BinComPred (Models.from_binop binop, v1, v2) |> sorted
    | _ ->
        Pred (Models.from_binop binop, [v1; v2])


  let make_physical_equals = make_binop

  let make_pred f args = Pred (f, args)

  let rec vals_of_path_cond = function
    | BinComPred (_, v1, v2) ->
        [v1; v2]
    | Pred (_, args) ->
        args
    | Not pc ->
        vals_of_path_cond pc
end

module MakePC (Val : S) = struct
  module ValSet = AbstractDomain.FiniteSet (Val)
  module PathCond = Make (Val)
  module PCSet = PrettyPrintable.MakePPSet (PathCond)
  module ConstMap = PrettyPrintable.MakePPMonoMap (Val) (Val)

  module InEqualMap = struct
    include PrettyPrintable.MakePPMonoMap (Val) (ValSet)

    let add_elt v c t =
      match find_opt v t with
      | Some consts ->
          add v (ValSet.add c consts) t
      | None ->
          add v (ValSet.singleton c) t
  end

  type t = {pc_set: PCSet.t; const_map: ConstMap.t; inequal_map: InEqualMap.t}

  let fold {pc_set; const_map; inequal_map} ~(f : PathCond.t -> 'a -> 'a) ~(init : 'a) =
    PCSet.fold f pc_set init
    |> ConstMap.fold (fun v c acc -> f (PathCond.BinComPred (Models.eq, v, c)) acc) const_map
    |> InEqualMap.fold
         (fun v consts acc ->
           ValSet.fold (fun c acc -> f (PathCond.BinComPred (Models.ne, v, c)) acc) consts acc )
         inequal_map


  let exists ~f {pc_set; const_map; inequal_map} =
    PCSet.exists f pc_set
    || ConstMap.exists (fun v c -> f (PathCond.BinComPred (Models.eq, v, c))) const_map
    || InEqualMap.exists
         (fun v consts -> ValSet.exists (fun c -> f (PathCond.BinComPred (Models.ne, v, c))) consts)
         inequal_map


  let all_values {pc_set; const_map; inequal_map} =
    List.concat_map (PCSet.elements pc_set) ~f:PathCond.vals_of_path_cond
    |> ValSet.of_list
    |> ConstMap.fold (fun v c acc -> ValSet.add v acc |> ValSet.add c) const_map
    |> InEqualMap.fold (fun v consts -> ValSet.add v consts |> ValSet.union) inequal_map
    |> ValSet.elements


  let empty = {pc_set= PCSet.empty; const_map= ConstMap.empty; inequal_map= InEqualMap.empty}

  let is_bottom {pc_set; const_map; inequal_map} =
    PCSet.is_empty pc_set && ConstMap.is_empty const_map && InEqualMap.is_empty inequal_map


  (* let compare pc1 pc2 = PCSet.compare (to_pc_set pc1) (to_pc_set pc2) *)

  let to_string {pc_set; const_map} =
    let const_map_str =
      ConstMap.fold
        (fun v c acc -> String.concat [acc; F.asprintf "(ConstMap) %a == %a@." Val.pp v Val.pp c])
        const_map ""
    in
    PCSet.fold
      (fun cond acc -> String.concat [acc; F.asprintf "(NonConst) %a@." PathCond.pp cond])
      pc_set const_map_str


  let pp fmt {const_map; pc_set; inequal_map} =
    F.fprintf fmt "@[<v 3>   * ConstMap:@,  %a@,* InequalMap:@,  %a@,* PathConds:@,  %a@]"
      ConstMap.pp const_map InEqualMap.pp inequal_map PCSet.pp pc_set


  let debug_if_invalid_pc transitives original_cond =
    match List.find transitives ~f:PathCond.is_invalid with
    | Some invalid ->
        L.d_printfln "Invalid condition %a generated by %a" PathCond.pp invalid PathCond.pp
          original_cond
    | None ->
        ()


  let filter_by_value ~f {pc_set; const_map; inequal_map} =
    let pc_set = PCSet.filter (PathCond.contains_with_pred ~f) pc_set in
    let const_map = ConstMap.filter (fun v c -> f v || f c) const_map in
    let inequal_map =
      InEqualMap.filter (fun v consts -> f v || ValSet.exists f consts) inequal_map
    in
    {pc_set; const_map; inequal_map}


  let update_const_map pc transitives =
    (* TODO: it may have scalability issues *)
    let const_map, inequal_map =
      PCSet.fold
        (fun cond (const_acc, inequal_acc) ->
          match cond with
          | PathCond.BinComPred (f, v, c) when Procname.equal f Models.eq && Val.is_concrete c ->
              (ConstMap.add v c const_acc, inequal_acc)
          | PathCond.Not (PathCond.BinComPred (f, v, c))
            when Procname.equal f Models.eq && Val.is_concrete c ->
              (const_acc, InEqualMap.add_elt v c inequal_acc)
          | _ ->
              (const_acc, inequal_acc) )
        transitives (pc.const_map, pc.inequal_map)
    in
    let pc_set =
      PCSet.map
        (* v -> c, v2 = v => v2 = c *)
        (PathCond.replace_by_map ~map:(fun v ->
             match ConstMap.find_opt v const_map with Some const -> const | None -> v ) )
        transitives
      (* remove trivial condition (e.g., c = c) *)
      |> PCSet.filter (not <<< PathCond.is_valid)
      (* remove constant inequal condition (e.g., v != c) *)
      |> PCSet.filter (function
           | PathCond.Not (PathCond.BinComPred (f, _, c))
             when Procname.equal f Models.eq && Val.is_concrete c ->
               false
           | _ ->
               true )
    in
    {pc_set; const_map; inequal_map}


  let update_pathcond_to_pc pathcond pc =
    match pathcond with
    | _ when PathCond.is_valid pathcond ->
        pc
    | PathCond.BinComPred (f, v, c) when Procname.equal f Models.eq && Val.is_concrete c ->
        {pc with const_map= ConstMap.add v c pc.const_map}
    | PathCond.BinComPred (f, v, c) when Procname.equal f Models.ne && Val.is_concrete c ->
        {pc with inequal_map= InEqualMap.add_elt v c pc.inequal_map}
    | _ ->
        {pc with pc_set= PCSet.add pathcond pc.pc_set}


  let compute_transitives pathcond ({pc_set; const_map; inequal_map} as pc) =
    match pathcond with
    | PathCond.BinComPred (f, v, c) when Procname.equal f Models.eq && Val.is_concrete c -> (
      match ConstMap.find_opt v const_map with
      | Some c' when Val.equal c c' ->
          (* already v = c, useless *)
          pc
      | Some c' ->
          (* already v = c', invalid *)
          let cond_gen = PathCond.make_physical_equals Binop.Eq c c' in
          if Config.debug_mode then
            debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Eq v c') ;
          {pc with pc_set= PCSet.add cond_gen pc_set}
      | None -> (
          let const_map' = ConstMap.add v c const_map in
          match InEqualMap.find_opt v inequal_map with
          | Some consts when ValSet.exists (Val.equal c) consts ->
              (* already v != c, invalid *)
              let cond_gen = PathCond.make_physical_equals Binop.Ne c c in
              if Config.debug_mode then
                debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Ne v c) ;
              {pc with pc_set= PCSet.add cond_gen pc_set; const_map= const_map'}
          | _ ->
              (* no inequal condition *)
              let inequal_map' = InEqualMap.remove v inequal_map in
              {pc with const_map= const_map'; inequal_map= inequal_map'} ) )
    | PathCond.Not (PathCond.BinComPred (f, v, c))
      when Procname.equal f Models.eq && Val.is_concrete c -> (
      match InEqualMap.find_opt v inequal_map with
      | Some consts when ValSet.mem c consts ->
          (* already v != c, useless *)
          pc
      | _ -> (
          let inequal_map' = InEqualMap.add_elt v c inequal_map in
          match ConstMap.find_opt v const_map with
          | Some c' when Val.equal c c' ->
              (* already v = c, invalid *)
              let cond_gen = PathCond.make_physical_equals Binop.Ne c c in
              if Config.debug_mode then
                debug_if_invalid_pc [cond_gen] (PathCond.make_physical_equals Binop.Eq v c) ;
              {pc with pc_set= PCSet.add cond_gen pc_set; inequal_map= inequal_map'}
          | Some _ ->
              (* already v = c', useless *)
              pc
          | None ->
              {pc with inequal_map= inequal_map'} ) )
    | _ ->
        pc


  let is_valid pathcond pc = PathCond.is_valid pathcond || exists pc ~f:(PathCond.equal pathcond)

  let is_invalid pc = exists pc ~f:PathCond.is_invalid

  let add pathcond pc =
    if PathCond.is_trivial pathcond then pc
    else if PathCond.is_invalid pathcond then {pc with pc_set= PCSet.add pathcond pc.pc_set}
    else compute_transitives (PathCond.normalize pathcond) pc


  let replace_by_map ~f pc = fold pc ~init:empty ~f:(add <<< PathCond.replace_by_map ~map:f)

  let meet pc1 pc2 = fold pc2 ~init:pc1 ~f:add

  let join pc1 pc2 =
    (* TODO: union for unconstrainted symbols *)
    let pc_set = PCSet.inter pc1.pc_set pc2.pc_set in
    let const_map =
      ConstMap.merge
        (fun _ c1_opt c2_opt ->
          match (c1_opt, c2_opt) with Some c1, Some c2 when Val.equal c1 c2 -> Some c1 | _ -> None
          )
        pc1.const_map pc2.const_map
    in
    let inequal_map =
      InEqualMap.merge
        (fun _ v1_opt v2_opt ->
          match (v1_opt, v2_opt) with
          | Some v1, Some v2 ->
              let v = ValSet.inter v1 v2 in
              if ValSet.is_empty v then None else Some v
          | _ ->
              None )
        pc1.inequal_map pc2.inequal_map
    in
    {pc_set; const_map; inequal_map}


  let check pc = fold pc ~init:Result.Valid ~f:(Result.conjunct <<< PathCond.check)

  let check_sat ?(print_unsat = false) pc1 pc2 =
    let pc_unioned = meet pc1 pc2 in
    let result = check pc_unioned |> Result.is_unsat in
    if print_unsat then
      L.progress "===== check sat =====@. - lhs: %a@. - rhs: %a@. - unioned: %a@. - result: %b@." pp
        pc1 pp pc2 pp pc_unioned result ;
    result


  let equal_values {const_map} v =
    (* only returns constant values *)
    match ConstMap.find_opt v const_map with Some const -> [v; const] | None -> [v]


  let equal_constant_opt {const_map} v = ConstMap.find_opt v const_map

  let inequal_values {inequal_map} v =
    match InEqualMap.find_opt v inequal_map with
    | Some consts ->
        ValSet.elements consts
    | None ->
        []


  let invalid = {empty with pc_set= PCSet.singleton PathCond.false_cond}
end
