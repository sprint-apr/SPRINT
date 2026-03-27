open! IStd
open! Vocab
module F = Format
module L = Logging
module Loc = BasicDom.Loc
module PowLoc = BasicDom.PowLoc
module PowProc = BasicDom.PowProc
module AbsTyp = BasicDom.AbsTyp
module Allocsite = BasicDom.Allocsite
module Hashtbl = Caml.Hashtbl
module CFG = ProcCfg.Exceptional
open FiptsAnalysisDomain

let ctx_map = ref Procname.Map.empty

let weak_update_ctx pid ctx =
  match Procname.Map.find_opt pid !ctx_map with
  | Some ctxs when Contexts.mem ctx ctxs ->
      ()
  | Some ctxs ->
      ctx_map := Procname.Map.add pid (Contexts.add ctx ctxs) !ctx_map
  | None ->
      ctx_map := Procname.Map.add pid (Contexts.singleton ctx) !ctx_map


(** compute fixed point *)
module Work = struct
  type t = Procname.t * Context.t [@@deriving compare]

  let pp fmt (p, ctx) = F.fprintf fmt "%a_%a" Procname.pp p Context.pp ctx

  let ctx_of (_, ctx) = ctx

  let pid_of (p, _) = p

  let make p ctx =
    weak_update_ctx p ctx ;
    (p, ctx)
end

module Worklist = PrettyPrintable.MakePPSet (Work)

let _cfgs = ref Procname.Map.empty

let wto_of pdesc : CFG.Node.t WeakTopologicalOrder.Partition.t =
  let proc = Procdesc.get_proc_name pdesc in
  match Procname.Map.find_opt proc !_cfgs with
  | Some wto ->
      wto
  | None ->
      let wto = ProcCfg.Exceptional.from_pdesc pdesc |> CFG.wto in
      _cfgs := Procname.Map.add proc wto !_cfgs ;
      wto


let _visited = ref Worklist.empty

let _clinits = ref Procname.Set.empty

let exec_node ~exec_instr program pid ctx node state =
  let instrs = Procdesc.Node.get_instrs node in
  Instrs.fold instrs ~init:state ~f:(exec_instr program pid ctx node)


let rec exec_wto ~exec_instr program pid ctx wto state =
  match (wto : CFG.Node.t WeakTopologicalOrder.Partition.t) with
  | Empty ->
      state
  | Node {node; next} ->
      let state = exec_node ~exec_instr program pid ctx node state in
      exec_wto ~exec_instr program pid ctx next state
  | Component {head; rest; next} ->
      exec_node ~exec_instr program pid ctx head state
      |> exec_wto ~exec_instr program pid ctx rest
      |> exec_node ~exec_instr program pid ctx head
      |> exec_wto ~exec_instr program pid ctx rest
      |> exec_node ~exec_instr program pid ctx head
      |> exec_wto ~exec_instr program pid ctx next


(* exec_wto  ~exec_instr program pid ctx next state *)

let exec_junit_pre ~exec_instr program (pid, ctx) state =
  match ctx with
  | Context.Empty testClass when Program.is_entry program pid ->
      let junit_node = Program.node_for_junit_premethods program testClass ~clinits:!_clinits pid in
      let instrs = Procdesc.Node.get_instrs junit_node in
      Instrs.fold instrs ~init:state ~f:(exec_instr program pid ctx junit_node)
  | _ ->
      state


let _stack = ref 0

let exec_work ~exec_instr program (pid, ctx) state =
  if Worklist.mem (pid, ctx) !_visited then state
  else (
    _visited := Worklist.add (pid, ctx) !_visited ;
    _stack := !_stack + 1 ;
    (* if !_stack > 40 then L.progress "too much stack %d@." !_stack ; *)
    weak_update_ctx pid ctx ;
    let pdesc = Program.pdesc_of program pid in
    let wto = wto_of pdesc in
    let result =
      exec_junit_pre ~exec_instr program (pid, ctx) state
      |> exec_wto ~exec_instr program pid ctx wto
    in
    _stack := !_stack - 1 ;
    result )


let pre_state = ref bottom

let same_locs = ref PowLoc.empty

(* ================ START of eval function ================= *)
let callees_of_node pid ctx node state =
  let instrs = Procdesc.Node.get_instrs node in
  Instrs.fold instrs ~init:Procname.Set.empty ~f:(fun acc instr ->
      match instr with
      | Sil.Call (_, fexp, _, _, _) ->
          let callees = eval_procs pid ctx fexp state in
          PowProc.fold (fun pid -> Procname.Set.add pid) callees acc
      | _ ->
          acc )


let points_to_list_of {mem} =
  Mem.fold
    (fun l v acc -> PowLoc.fold (fun l_to acc -> (l, l_to) :: acc) (Val.get_locs v) acc)
    mem []


let callees_of_instr program state (pid : Procname.t) ctx instr_node : PowProc.t =
  match InstrNode.get_instr instr_node with
  | Sil.Call (_, Const (Cfun callee), [(this_exp, this_typ); _], _, _)
  | Sil.Call (_, Const (Cfun callee), [_; (this_exp, this_typ); _], _, _)
    when String.equal (Procname.get_method callee) "assertEquals" ->
      let this_locs = eval_locs pid ctx this_exp state in
      PowLoc.fold
        (fun loc acc ->
          let this_typ =
            match AbsTyp.typ_of (type_of_loc state loc) with
            | typ ->
                typ
            | exception Caml.Not_found ->
                this_typ
          in
          match Program.find_equals_proc this_typ with
          | Some equals_proc ->
              PowProc.add equals_proc acc
          | None ->
              acc )
        this_locs PowProc.empty
  | Sil.Call (_, Const (Cfun callee), _, _, _) when Program.is_library_call program instr_node ->
      PowProc.singleton callee
  | Sil.Call (_, fexp, (this_exp, _) :: _, loc, {cf_virtual}) as instr when cf_virtual ->
      resolve_callees state pid ctx ~fexp ~this_exp instr loc
  | Sil.Call (_, fexp, _, _, _) ->
      eval_procs pid ctx fexp state
  | _ ->
      PowProc.empty


let rec exec_model program pid ctx callee node instr (ret_id, ret_typ) arg_typs
    ({reg; loc2typ} as state) =
  let callee_name = Procname.get_method callee in
  let ret_loc = Loc.of_id ~ctx (ret_id, pid) in
  match (instr, FiptsAnalysisModels.dispatch callee (List.unzip arg_typs |> snd)) with
  | Sil.Call (_, Const (Cfun proc), [(Exp.Sizeof {typ= {desc= Tarray _} as typ}, _)], _, _), _
    when (is_new proc && is_primitive_typ typ) || Procname.is_java_class_initializer pid ->
      (* when is_new proc && is_primitive_typ typ -> *)
      let allocsite =
        Allocsite.of_typ ~is_exact:false object_typ |> Loc.of_allocsite ~ctx:(Context.empty_of ctx)
      in
      {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) reg}
  | Sil.Call (_, Const (Cfun proc), [(Exp.Sizeof {typ}, _)], _, _), _
    when is_new proc && is_primitive_typ typ ->
      let allocsite =
        Allocsite.of_typ ~is_exact:true typ |> Loc.of_allocsite ~ctx:(Context.empty_of ctx)
      in
      {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) reg}
  | Sil.Call ((_, _), Const (Cfun proc), [(Exp.Sizeof _, _)], _, _), _ when is_new proc ->
      let allocsite = make_allocsite (Context.empty_of ctx) node instr in
      let value = Val.of_locs (PowLoc.singleton allocsite) in
      {state with reg= Reg.weak_update ret_loc value reg}
  | _, Some exec ->
      let exec_work = exec_work ~exec_instr program in
      exec pid ~exec_work ctx node instr (ret_loc, ret_typ) arg_typs state
  | Sil.Call (_, _, [(_, arg_typ)], _, {cf_virtual}), _
    when cf_virtual && Typ.is_pointer arg_typ && String.is_prefix callee_name ~prefix:"get" -> (
    match Val.default_of_typ ~is_exact:false ~ctx:(Context.empty_of ctx) ret_typ with
    | Some value ->
        let this_exp, _ = List.hd_exn arg_typs in
        let fieldname =
          String.chop_prefix_exn (Procname.get_method callee) ~prefix:"get" |> String.uncapitalize
        in
        let field_class = Typ.Name.Java.from_string (String.capitalize fieldname) in
        let field_name = Fieldname.make field_class fieldname in
        let this_locs = eval_locs pid ctx this_exp state in
        let this_field_locs = PowLoc.append_fields this_locs ~fn:field_name in
        {state with reg= Reg.weak_update ret_loc value reg}
        |> weak_update_mem_locs this_field_locs value
    | None ->
        state )
  | _ -> (
    match Val.default_of_typ ~is_exact:false ~ctx:(Context.empty_of ctx) ret_typ with
    | Some value ->
        let loc = Val.get_locs value |> PowLoc.choose in
        state.loc2typ <- Loc2Typ.add_typ loc2typ loc (Typ.strip_ptr ret_typ) ;
        {state with reg= Reg.weak_update ret_loc value reg}
    | None ->
        (* L.progress "could not find default value for %a at %a@." (Typ.pp_full Pp.text) ret_typ InstrNode.pp
           (InstrNode.of_pnode node instr) ; *)
        state )


and exec_call program pid ctx callee node instr (ret_id, ret_typ) actuals state =
  let formal_bound =
    if Program.is_undef_proc program callee then state
    else
      let formals = Procdesc.get_formals (Program.pdesc_of program callee) in
      if Int.equal (List.length formals) (List.length actuals) then (
        let callee_ctx = Context.append program ctx (InstrNode.of_pnode node instr) pid callee in
        weak_update_ctx callee callee_ctx ;
        List.fold2_exn
          ~f:(fun acc (name, typ) (actual, _) ->
            bind_actual program pid ctx callee node instr (name, typ) actual acc )
          ~init:state formals actuals )
      else state
  in
  let retval_bound =
    bind_retvar program pid ctx callee node instr actuals (ret_id, ret_typ) formal_bound
  in
  retval_bound


and bind_actual program pid ctx callee node instr (name, _) (actual : Exp.t) state =
  let callee_ctx = Context.append program ctx (InstrNode.of_pnode node instr) pid callee in
  weak_update_ctx callee callee_ctx ;
  let loc_formal = Loc.of_pvar ~ctx:callee_ctx (Pvar.mk name callee) in
  let value_of_actual = eval pid ctx actual state in
  let state_before_callee = weak_update_mem loc_formal value_of_actual state in
  exec_work ~exec_instr program (callee, callee_ctx) state_before_callee


and bind_retvar program pid ctx callee node instr _ (ret_id, _) ({reg; mem} as state) =
  let callee_ctx = Context.append program ctx (InstrNode.of_pnode node instr) pid callee in
  let ret_pvar = Pvar.get_ret_pvar callee in
  let ret_pvar_loc = Loc.of_pvar ~ctx:callee_ctx ret_pvar in
  let ret_value = Mem.find ret_pvar_loc mem in
  {state with reg= Reg.weak_update (Loc.of_id ~ctx (ret_id, pid)) ret_value reg}


and exec_instr program pid ctx node ({reg; mem} as state) instr =
  let instr_node = InstrNode.of_pnode node instr in
  match instr with
  | Sil.Load {id} when Ident.is_none id ->
      (* for efficiency *)
      state
  | Sil.Load {id; e} ->
      let locs = eval_locs pid ctx e state in
      let value = Mem.find_mem_set locs mem in
      (* let _ =
           if PowLoc.cardinal locs > 100 then
             if mode_allocsite then
               let _ = L.progress "too many locs (%d) at %a@." (PowLoc.cardinal locs) InstrNode.pp instr_node in
               raise (Unexpected "TooManyAllocs")
             else L.progress "too many locs (%d) at %a@." (PowLoc.cardinal locs) InstrNode.pp instr_node
         in *)
      {state with reg= Reg.weak_update (Loc.of_id ~ctx (id, pid)) value reg}
  | Sil.Store {e1; e2} ->
      let value = eval pid ctx e2 state in
      let locs = eval_locs pid ctx e1 state in
      weak_update_mem_locs locs value state
  | Sil.Call (ret, Const (Cfun callee), actuals, _, _)
    when String.equal (Procname.get_method callee) "assertEquals" ->
      let callees = callees_of_instr program state pid ctx instr_node in
      PowProc.fold
        (fun callee -> exec_call program pid ctx callee node instr ret actuals)
        callees state
  | Sil.Call (ret, _, actuals, _, _) ->
      let callees = callees_of_instr program state pid ctx instr_node in
      PowProc.fold
        (fun callee ->
          if Program.is_undef_proc program callee then
            exec_model program pid ctx callee node instr ret actuals
          else exec_call program pid ctx callee node instr ret actuals )
        callees state
  | _ ->
      state


let rec tabulation program state worklist =
  _visited := Worklist.empty ;
  let newstate = Worklist.fold (exec_work ~exec_instr program) worklist state in
  let nextworks =
    Procname.Map.fold
      (fun pid ctxs -> Contexts.fold (fun ctx -> Worklist.add (Work.make pid ctx)) ctxs)
      !ctx_map worklist
  in
  if leq ~lhs:newstate ~rhs:state && Worklist.subset nextworks worklist then newstate
  else
    let {mem} = newstate in
    L.progress "-- # of total locations : %d@." (Mem.cardinal mem) ;
    tabulation program newstate nextworks


let do_pointer_analysis ~entries program =
  (* let nodes = Program.all_nodes program in
     L.progress "-- total nodes of program: %d@." (List.length nodes) ; *)
  (* fixpoint iteration *)
  let initial_worklist =
    Procname.Set.fold
      (fun pid ->
        let ctxs_visited = DynInfo.ctxs_of_proc_visited pid in
        Contexts.fold (fun ctx -> Worklist.add (Work.make pid ctx)) ctxs_visited )
      entries Worklist.empty
  in
  L.progress "initial worklists: %a@." Worklist.pp initial_worklist ;
  if Config.debug_mode then
    L.progress "=== Is_model_in_all_proc ===========@.%a@." Procname.Set.pp
      (Procname.Set.filter
         (fun pid -> Program.is_undef_proc program pid)
         (Program.all_procs program) ) ;
  tabulation program bottom initial_worklist
