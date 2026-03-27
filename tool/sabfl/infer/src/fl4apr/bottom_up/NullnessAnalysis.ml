open! Vocab
module F = Format
module L = Logging
module CFG = ProcCfg.Normal
module Node = InstrNode
module Models = BasicDom.Models

module AP = struct
  include AccessPath

  let compare (((v1, _), _) : t) (((v2, _), _) : t) = Var.compare v1 v2

  let equal = [%compare.equal: t]

  let is_return : t -> bool = fun ((var, _), _) -> Var.is_return var
end

module IdMap = PrettyPrintable.MakePPMonoMap (Ident) (AP)
module Val = Program.AbsConst

module Mem = struct
  include PrettyPrintable.MakePPMonoMap (AP) (Val)

  let add ap v t = if Val.is_nonconst v then t else add ap v t

  let join =
    merge (fun _ v1_opt v2_opt ->
        match (v1_opt, v2_opt) with
        | Some v1, Some v2 ->
            let joined = Val.join v1 v2 in
            if Val.is_nonconst joined then None else Some joined
        | _ ->
            None )
end

module Reg = struct
  include PrettyPrintable.MakePPMonoMap (Ident) (Val)

  let add ap v t = if Val.is_nonconst v then t else add ap v t

  let join =
    merge (fun _ v1_opt v2_opt ->
        match (v1_opt, v2_opt) with
        | Some v1, Some v2 ->
            let joined = Val.join v1 v2 in
            if Val.is_nonconst joined then None else Some joined
        | _ ->
            None )
end

module Domain = struct
  type t = {mem: Mem.t; reg: Reg.t; idmap: IdMap.t}

  let pp fmt {mem; reg; idmap} =
    F.fprintf fmt "@[Nonnull mem:@, - %a@, reg:@, - %a@, Idmap:@, - %a@]" Mem.pp mem Reg.pp reg
      IdMap.pp idmap


  let leq ~lhs ~rhs =
    Mem.equal Val.equal lhs.mem rhs.mem
    && Reg.equal Val.equal lhs.reg rhs.reg
    && IdMap.for_all (fun id _ -> IdMap.mem id rhs.idmap) lhs.idmap


  let join lhs rhs =
    { mem= Mem.join lhs.mem rhs.mem
    ; reg= Reg.join lhs.reg rhs.reg
    ; idmap= IdMap.union (fun _ ap1 _ -> Some ap1) lhs.idmap rhs.idmap }


  let widen ~prev ~next ~num_iters:_ = join prev next

  let add_id astate id v =
    match IdMap.find_opt id astate.idmap with
    | Some ap ->
        {astate with reg= Reg.add id v astate.reg; mem= Mem.add ap v astate.mem}
    | None ->
        {astate with reg= Reg.add id v astate.reg}


  let add_nonnull_id astate id =
    match IdMap.find_opt id astate.idmap with
    | Some ap ->
        {astate with reg= Reg.add id NonNull astate.reg; mem= Mem.add ap NonNull astate.mem}
    | None ->
        {astate with reg= Reg.add id NonNull astate.reg}


  let to_summary proc_desc astate =
    let ret_pv, ret_typ = (Procdesc.get_ret_var proc_desc, Procdesc.get_ret_type proc_desc) in
    let ret_ap = AP.of_pvar ret_pv ret_typ in
    Mem.find_opt ret_ap astate.mem


  let bottom = {mem= Mem.empty; idmap= IdMap.empty; reg= Reg.empty}

  let init pdesc =
    let formals = Procdesc.get_pvar_formals pdesc in
    List.fold formals ~init:bottom ~f:(fun astate (pv, typ) ->
        if Pvar.is_this pv then {astate with mem= Mem.add (AP.of_pvar pv typ) NonNull astate.mem}
        else astate )


  let rec ap_opt_of_exp t (e : Exp.t) typ : AP.t option =
    match e with
    | Lvar pv ->
        Some (AP.of_pvar pv typ)
    | Lfield (Var id, fn, _) -> (
      match IdMap.find_opt id t.idmap with
      | Some (base, accs) ->
          Some (base, accs @ [AP.FieldAccess fn])
      | None ->
          None )
    | Cast (typ, e) ->
        ap_opt_of_exp t e typ
    | _ ->
        None


  let rec is_sub_ap ~(sub : AP.access list) (sup : AP.access list) =
    match (sub, sup) with
    | [], _ ->
        true
    | _ :: _, [] ->
        false
    | hd1 :: accs1, hd2 :: accs2 when AP.equal_access hd1 hd2 ->
        is_sub_ap ~sub:accs1 accs2
    | _ ->
        false


  let add_ap ap v t = {t with mem= Mem.add ap v t.mem}

  let remove_ap (base1, accs1) t =
    let mem =
      Mem.filter
        (fun (base2, accs2) _ -> not (AP.equal_base base1 base2 && is_sub_ap ~sub:accs1 accs2))
        t.mem
    in
    {t with mem}


  let rec eval t : Exp.t -> Val.t option = function
    | Const c ->
        Some (Primitive c)
    | Cast (_, e) ->
        eval t e
    | Var id ->
        Reg.find_opt id t.reg
    | Lfield _ | Lindex _ | Lvar _ ->
        None
    | Sizeof _ | Closure _ | Exn _ | BinOp _ | UnOp _ ->
        (* non-pointer exp *)
        None
end

let rec is_nonnull_exp : Exp.t -> bool = function
  | Const (Cint intlit) ->
      not (IntLit.isnull intlit)
  | Const (Cstr _) ->
      true
  | Const _ ->
      true
  | Cast (_, e) ->
      is_nonnull_exp e
  | Var _ | Lfield _ | Lindex _ | Lvar _ ->
      false
  | Sizeof _ | Closure _ | Exn _ | BinOp _ | UnOp _ ->
      (* non-pointer exp *)
      false


let nonnull_methods =
  [ "getClass"
  ; "toString"
  ; "trim"
  ; "intern"
  ; "getStackTrace"
  ; "getMessage"
  ; "getSuppressed"
  ; "getLocalizedMessage"
  ; "clone"
  ; "getCountry"
  ; "getName"
  ; "chars"
  ; "codePoints" ]


let is_nonnull_mthd mthd args =
  let name = Procname.Java.get_class_type_name mthd in
  if List.mem nonnull_methods ~equal:String.equal (Procname.Java.get_method mthd) then true
  else if Fl4aprModels.implements_interfaces ["java.util.Locale"] name then List.length args <= 1
  else if Fl4aprModels.Lang.implements name then true
  else if Fl4aprModels.Class.implements name then
    not
      (List.mem
         ["getPackage"; "getClassLoader"; "getSuperclass"; "getGenericSuperclasss"]
         ~equal:String.equal (Procname.Java.get_method mthd) )
  else if Fl4aprModels.Map.implements name then
    List.mem ~equal:String.equal
      [ "values"
      ; "entrySet"
      ; "keySet"
      ; "navigableKeySet"
      ; "lastKey"
      ; "firstKey"
      ; "descendingMap"
      ; "descendingKeySet"
      ; "comparator" ]
      (Procname.Java.get_method mthd)
  else if Fl4aprModels.Collection.implements name then
    not (String.is_prefix (Procname.Java.get_method mthd) ~prefix:"get")
  else false


module Semantics = struct
  module CFG = CFG
  module Domain = Domain

  type analysis_data = {program: Program.t; analyze_dependency: Procname.t -> Val.t option}

  type instr = Sil.instr

  let analysis_data_from program analyze_dependency = {program; analyze_dependency}

  let value_of_callee analysis_data callee =
    match analysis_data.analyze_dependency callee with
    | Some summary ->
        L.d_printfln "callee %a has constant value %a" Procname.pp callee Val.pp summary ;
        Some summary
    | None when Program.is_undef_proc analysis_data.program callee ->
        L.d_printfln "callee %a is extern method" Procname.pp callee ;
        None
    | None ->
        L.d_printfln "no constant return found for %a" Procname.pp callee ;
        None


  let exec_instr (astate : Domain.t) analysis_data _ instr =
    match instr with
    | Sil.Load {id; e= Lfield (_, fn, _)} when Program.is_nonnull_static_final_field fn ->
        Domain.add_id astate id NonNull
    | Sil.Load {id; e; typ} -> (
      match Domain.ap_opt_of_exp astate e typ with
      | Some ap -> (
        match Mem.find_opt ap astate.mem with
        | Some v ->
            {astate with idmap= IdMap.add id ap astate.idmap; reg= Reg.add id v astate.reg}
        | None ->
            {astate with idmap= IdMap.add id ap astate.idmap} )
      | None ->
          astate )
    | Sil.Store {e1; e2; typ} -> (
      match (Domain.ap_opt_of_exp astate e1 typ, Domain.eval astate e2) with
      | Some ap, Some v ->
          Domain.remove_ap ap astate |> Domain.add_ap ap v
      | Some ap, None ->
          Domain.remove_ap ap astate
      | None, _ ->
          astate )
    | Sil.Call ((ret_id, _), Const (Cfun (Procname.Java mthd)), args, _, _)
      when is_nonnull_mthd mthd args ->
        {astate with reg= Reg.add ret_id NonNull astate.reg}
    | Sil.Call ((ret_id, _), Const (Cfun proc), _, _, _) when is_new proc ->
        {astate with reg= Reg.add ret_id NonNull astate.reg}
    | Sil.Call ((_, ret_typ), Const (Cfun _), _, _, _) when Typ.is_void ret_typ ->
        astate
    | Sil.Call ((ret_id, _), Const (Cfun (Java mthd)), _, _, _) -> (
        let callees =
          Program.callee_dispatch
            ~base_class:(Procname.Java.get_class_type_name mthd)
            ~is_exact:false mthd
        in
        if Procname.Set.is_empty callees then (
          L.d_printfln "no callee found" ;
          astate )
        else
          let callee = Procname.Set.choose callees in
          let v =
            Procname.Set.fold
              (fun callee acc ->
                match (value_of_callee analysis_data callee, acc) with
                | Some v1, Some v2 when Val.equal v1 v2 ->
                    Some v1
                | _ ->
                    None )
              callees
              (value_of_callee analysis_data callee)
          in
          match v with Some v -> {astate with reg= Reg.add ret_id v astate.reg} | None -> astate )
    | Sil.Call _ ->
        astate
    | Sil.Metadata (ExitScope (vars, _)) ->
        List.fold ~init:astate vars ~f:(fun astate var ->
            match var with
            | Var.LogicalVar id ->
                Domain.
                  {astate with reg= Reg.remove id astate.reg; idmap= IdMap.remove id astate.idmap}
            | _ ->
                astate )
    | Sil.Metadata _ ->
        astate
    | Sil.Prune (BinOp (Binop.Eq, Var id1, Var id2), _, _, _) when Reg.mem id2 astate.reg ->
        Domain.add_nonnull_id astate id1
    | Sil.Prune (UnOp (Unop.LNot, BinOp (Binop.Ne, Var id1, Var id2), _), _, _, _)
      when Reg.mem id2 astate.reg ->
        Domain.add_nonnull_id astate id1
    | Sil.Prune (BinOp (Binop.Ne, Var id, Exp.Const (Cint intlit)), _, _, _)
      when IntLit.isnull intlit ->
        Domain.add_nonnull_id astate id
    | Sil.Prune (UnOp (Unop.LNot, BinOp (Binop.Eq, Var id, Exp.Const (Cint intlit)), _), _, _, _)
      when IntLit.isnull intlit ->
        Domain.add_nonnull_id astate id
    | Sil.Prune _ ->
        astate


  let pp_session_name node fmt =
    F.fprintf fmt "===== Nullness Analysis (%a) ====@." Procdesc.Node.pp
      (CFG.Node.underlying_node node)
end

module Analyzer = AbstractInterpreter.MakeWTO (Semantics)

let compute_invariant_map ~initial analysis_data proc_desc : Analyzer.invariant_map =
  Analyzer.exec_pdesc ~do_narrowing:false ~initial analysis_data proc_desc


let compute_summary : Procdesc.t -> CFG.t -> Analyzer.invariant_map -> Val.t option =
 fun pdesc cfg inv_map ->
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some exit_state ->
      Domain.to_summary pdesc exit_state
  | None ->
      None


let checker {InterproceduralAnalysis.analyze_dependency; proc_desc} =
  if Config.sprint_preanal then
    let interproc callee =
      match analyze_dependency callee with Some (_, summary) -> Some summary | None -> None
    in
    let program = Program.from_marshal () in
    let analysis_data = Semantics.analysis_data_from program interproc in
    let cfg = CFG.from_pdesc proc_desc in
    let initial = Domain.init proc_desc in
    let inv_map = compute_invariant_map ~initial analysis_data proc_desc in
    compute_summary proc_desc cfg inv_map
  else None
