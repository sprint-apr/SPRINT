open! IStd
open! Vocab
module L = Logging
module Node = InterNode
module NSet = PrettyPrintable.MakePPSet (Node)
module Hashtbl = Caml.Hashtbl

module IntraCfg = struct
  module G = Graph.Imperative.Digraph.ConcreteBidirectional (Node)
  module InstrG = Graph.Imperative.Digraph.ConcreteBidirectional (InstrNode)
  module GDom = Graph.Dominator.Make_graph (G)
  module Oper = Graph.Oper.I (G)
  module Path = Graph.Path.Check (G)

  type t =
    { pdesc: Procdesc.t
    ; file: SourceFile.t
    ; graph: G.t
    ; mutable instr_graph: InstrG.t option
    ; mutable cfg_path_checker: Path.path_checker option
    ; mutable cfg_dom_tree: (G.t * Path.path_checker) option
    ; mutable cfg_pdom_tree: (G.t * Path.path_checker) option }

  let compute_dom_tree ~is_post pdesc cfg =
    let entry =
      pdesc
      |> (if is_post then Procdesc.get_exit_node else Procdesc.get_start_node)
      |> Node.of_pnode
    in
    let cfg = if is_post then Oper.mirror cfg else cfg in
    let GDom.{dom_tree} = GDom.compute_all cfg entry in
    let graph = G.create () in
    G.iter_vertex
      (fun v ->
        G.add_vertex graph v ;
        List.iter (dom_tree v) ~f:(G.add_edge graph v) )
      cfg ;
    (graph, Path.create graph)


  let instr_graph_from_pdesc pdesc =
    let graph = InstrG.create () in
    let nodes =
      let pnodes = Procdesc.get_nodes pdesc in
      List.concat_map pnodes ~f:InstrNode.list_of_pnode
    in
    (* ignore procedures without body nodes *)
    if List.length nodes < 3 then graph
    else
      let add_succs node = List.iter (InstrNode.get_succs node) ~f:(InstrG.add_edge graph node) in
      List.iter nodes ~f:add_succs ;
      graph


  let from_pdesc pdesc =
    let g = G.create () in
    let insert_skip_instr_to_empty_node n =
      if Instrs.is_empty (Procdesc.Node.get_instrs n) then
        let instr_to_add = Sil.skip_instr in
        Procdesc.Node.replace_instrs_with_given n (Instrs.singleton instr_to_add)
    in
    Procdesc.iter_nodes
      (fun node ->
        insert_skip_instr_to_empty_node node ;
        (* print_node node ; *)
        List.iter (Procdesc.Node.get_succs node) ~f:(fun succ ->
            G.add_edge_e g (Node.of_pnode node, Node.of_pnode succ) ) )
      pdesc ;
    let Location.{file} = Procdesc.get_loc pdesc in
    { pdesc
    ; file
    ; graph= g
    ; instr_graph= None
    ; cfg_path_checker= None
    ; cfg_dom_tree= None
    ; cfg_pdom_tree= None }


  let pred {graph} x = G.pred graph x

  let succ {graph} x = G.succ graph x

  let get_instr_graph t =
    match t.instr_graph with
    | Some instr_graph ->
        instr_graph
    | None ->
        t.instr_graph <- Some (Profiler.pick "draw instr_graph" instr_graph_from_pdesc t.pdesc) ;
        Option.value_exn t.instr_graph


  let get_cfg_path_checker t =
    match t.cfg_path_checker with
    | Some cfg_path_checker ->
        cfg_path_checker
    | None ->
        t.cfg_path_checker <- Some (Profiler.pick "create path" Path.create t.graph) ;
        Option.value_exn t.cfg_path_checker


  let get_cfg_dom_tree t =
    match t.cfg_dom_tree with
    | Some cfg_dom_tree ->
        cfg_dom_tree
    | None ->
        t.cfg_dom_tree <-
          Some (Profiler.pick "compute_dom_tree" (compute_dom_tree ~is_post:false t.pdesc) t.graph) ;
        Option.value_exn t.cfg_dom_tree


  let get_cfg_pdom_tree t =
    match t.cfg_pdom_tree with
    | Some cfg_pdom_tree ->
        cfg_pdom_tree
    | None ->
        t.cfg_pdom_tree <-
          Some (Profiler.pick "compute_pdom_tree" (compute_dom_tree ~is_post:true t.pdesc) t.graph) ;
        Option.value_exn t.cfg_pdom_tree


  let pred_instr_node t x = InstrG.pred (get_instr_graph t) x

  let succ_instr_node t x = InstrG.succ (get_instr_graph t) x

  (* let iter_nodes {pdesc} ~f = Procdesc.iter_nodes f pdesc *)

  (* let fold_nodes {pdesc} ~f = Procdesc.fold_nodes f pdesc *)

  let is_reachable t x y = Path.check_path (get_cfg_path_checker t) x y

  let dom t x y = Path.check_path (snd (get_cfg_dom_tree t)) x y

  let pdom t x y = Path.check_path (snd (get_cfg_pdom_tree t)) x y

  let[@warning "-32"] mem_vertex {graph} = G.mem_vertex graph

  let find_reachable_nodes_of ?(forward = true) ?(reflexive = true) (graph : G.t) (init : NSet.t) :
      NSet.t =
    let fold_next = if forward then G.fold_succ else G.fold_pred in
    let rec __reach reachables wset =
      if NSet.is_empty wset then reachables
      else
        let w = NSet.choose wset in
        let rest = NSet.remove w wset in
        if G.mem_vertex graph w then
          let new_reachables =
            fold_next
              (fun succ acc -> if NSet.mem succ reachables then acc else NSet.add succ acc)
              graph w NSet.empty
          in
          __reach (NSet.union reachables new_reachables) (NSet.union new_reachables rest)
        else (* L.progress "%a is not in the graph!.@" Node.pp w ; *)
          __reach reachables rest
    in
    if reflexive then __reach init init else __reach NSet.empty init
end

module CallGraph = struct
  include
    Graph.Imperative.Digraph.ConcreteBidirectionalLabeled
      (struct
        include Procname

        let hash x = Hashtbl.hash (Procname.hashable_name x)
      end)
      (InstrNode)

  let find_reachable_nodes_of ?(forward = true) ?(reflexive = true) (graph : t)
      (init : Procname.Set.t) : Procname.Set.t =
    let fold_next = if forward then fold_succ else fold_pred in
    let rec __reach reachables wset =
      if Procname.Set.is_empty wset then reachables
      else
        let w = Procname.Set.choose wset in
        let rest = Procname.Set.remove w wset in
        if mem_vertex graph w then
          let new_reachables =
            fold_next
              (fun succ acc ->
                if Procname.Set.mem succ reachables then acc else Procname.Set.add succ acc )
              graph w Procname.Set.empty
          in
          __reach
            (Procname.Set.union reachables new_reachables)
            (Procname.Set.union new_reachables rest)
        else (* L.progress "%a is not in the graph!.@" Procname.pp w ; *)
          __reach reachables rest
    in
    if reflexive then __reach init init else __reach Procname.Set.empty init
end

module Dot = Graph.Graphviz.Dot (struct
  include CallGraph

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = Procname.to_string v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes (_, instr_node, _) = [`Label (F.asprintf "%a" InstrNode.pp instr_node)]
end)

module ClassHierachy = struct
  include Graph.Imperative.Digraph.ConcreteBidirectional (Typ.Name)

  let find_reachable_nodes_of ?(forward = true) ?(reflexive = true) (graph : t)
      (init : Typ.Name.Set.t) : Typ.Name.Set.t =
    let fold_next = if forward then fold_succ else fold_pred in
    let rec __reach reachables wset =
      if Typ.Name.Set.is_empty wset then reachables
      else
        let w = Typ.Name.Set.choose wset in
        let rest = Typ.Name.Set.remove w wset in
        if mem_vertex graph w then
          let new_reachables =
            fold_next
              (fun succ acc ->
                if Typ.Name.Set.mem succ reachables then acc else Typ.Name.Set.add succ acc )
              graph w Typ.Name.Set.empty
          in
          __reach
            (Typ.Name.Set.union reachables new_reachables)
            (Typ.Name.Set.union new_reachables rest)
        else (* L.progress "%a is not in the graph!.@" Typ.Name.pp w ; *)
          __reach reachables rest
    in
    if reflexive then __reach init init else __reach Typ.Name.Set.empty init
end

module ClassHierachyDot = Graph.Graphviz.Dot (struct
  include ClassHierachy

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = Typ.Name.name v

  let vertex_attributes _ = []

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes (_, _) = [`Label ""]
end)

module ParamField = struct
  type t = int * Fieldname.t [@@deriving compare]

  let pp fmt (i, fn) = F.fprintf fmt "%d.%a" i Fieldname.pp fn
end

module ParamFields = AbstractDomain.FiniteSet (ParamField)
module SideEffects = WeakMap.Make (Procname) (ParamFields)

module type AbsConstS = sig
  type t = NonNull | Primitive of Const.t | NonConst [@@deriving compare, equal]

  val pp : Formatter.t -> t -> unit

  val is_nonnull : t -> bool

  val is_nonconst : t -> bool

  val join : t -> t -> t
end

module AbsConst = struct
  type t = NonNull | Primitive of Const.t | NonConst [@@deriving compare, equal]

  let pp fmt = function
    | NonNull ->
        F.fprintf fmt "NonNull"
    | Primitive const ->
        (Const.pp Pp.text) fmt const
    | NonConst ->
        F.fprintf fmt "NonConst"


  let is_nonnull = function
    | NonNull ->
        true
    | Primitive (Cstr _ | Cclass _ | Cfun _) ->
        true
    | _ ->
        false


  let is_constant = function Primitive _ -> true | _ -> false

  let is_nonconst = function NonConst -> true | _ -> false

  let join lhs rhs =
    if equal lhs rhs then lhs else if is_nonnull lhs && is_nonnull rhs then NonNull else NonConst
end

type t =
  { mutable cfgs: IntraCfg.t Procname.Map.t
  ; tenv: Tenv.t
  ; classes: ClassHierachy.t
  ; callgraph: CallGraph.t
  ; field_info: (Fieldname.t, field_info) Hashtbl.t
  ; all_nodes: InterNode.t list
  ; all_procs: Procname.Set.t
  ; mutable important_param_typs: (Exp.t * Typ.Name.Set.t) Procname.Map.t
  ; mutable library_calls: InstrNode.Set.t
  ; mutable class_inits: Procname.t list (* executed first *)
  ; mutable entries: Procname.t list (* execute @Before, then @TEST *)
  ; mutable return_values: AbsConst.t Procname.Map.t
  ; mutable side_effects: SideEffects.t }

and field_info =
  { typ: Typ.t
  ; annotations: Annot.Item.t
  ; access: PredSymb.access
  ; is_static: bool
  ; is_final: bool
  ; initialization: Exp.t Option.t }

let get_entries {entries} = entries

let is_entry {entries} proc = List.mem entries ~equal:Procname.equal proc

let add_call_edge {callgraph} instr_node callee =
  CallGraph.add_edge_e callgraph (InstrNode.get_proc_name instr_node, instr_node, callee)


let add_param_typs t proc (e, names) =
  t.important_param_typs <- Procname.Map.add proc (e, names) t.important_param_typs


let reset_cg program = {program with callgraph= CallGraph.create ()}

let print_callgraph program dotname =
  Utils.with_file_out dotname ~f:(fun oc -> Dot.output_graph oc program.callgraph)


let print_classhierachy program dotname =
  Utils.with_file_out dotname ~f:(fun oc -> ClassHierachyDot.output_graph oc program.classes)


let print_param_typs program filename =
  let msg =
    F.asprintf "%a"
      (Procname.Map.pp ~pp_value:(Pp.pair ~fst:Exp.pp ~snd:Typ.Name.Set.pp))
      program.important_param_typs
  in
  print_to_file ~dirname:None ~msg ~filename


let callers_of_instr_node {callgraph} instr_node =
  let preds = try CallGraph.pred_e callgraph (InstrNode.get_proc_name instr_node) with _ -> [] in
  List.filter_map preds ~f:(fun (pred, instr_node', _) ->
      if InstrNode.equal instr_node instr_node' then Some pred else None )


let callees_of_instr_node {callgraph} instr_node =
  match InstrNode.get_instr instr_node with
  | Sil.Call (_, _, _, _, {cf_virtual}) when cf_virtual ->
      let succs =
        try CallGraph.succ_e callgraph (InstrNode.get_proc_name instr_node) with _ -> []
      in
      List.filter_map succs ~f:(fun (_, instr_node', succ) ->
          if InstrNode.equal instr_node instr_node' then Some succ else None )
  | Sil.Call (_, Const (Cfun procname), _, _, _)
    when List.mem ["start"; "submit"] ~equal:String.equal (Procname.get_method procname) ->
      let succs =
        try CallGraph.succ_e callgraph (InstrNode.get_proc_name instr_node) with _ -> []
      in
      List.filter_map succs ~f:(fun (_, instr_node', succ) ->
          if InstrNode.equal instr_node instr_node' then Some succ else None )
  | Sil.Call (_, Const (Cfun procname), _, _, _) ->
      [procname]
  | _ ->
      []


let callers_of_proc {callgraph} proc =
  if CallGraph.mem_vertex callgraph proc then CallGraph.pred callgraph proc
  else (* L.progress "%a is not in callgraph!@." Procname.pp proc ; *)
    []


let callees_of_proc {callgraph} proc =
  if CallGraph.mem_vertex callgraph proc then CallGraph.succ callgraph proc
  else (* L.progress "%a is not in callgraph!@." Procname.pp proc ; *)
    []


let cfgof {cfgs} pid = Procname.Map.find pid cfgs

let pdesc_of_opt {cfgs} pid =
  match Procname.Map.find_opt pid cfgs with Some IntraCfg.{pdesc} -> Some pdesc | None -> None


let pdesc_of t pid =
  match pdesc_of_opt t pid with
  | Some pdesc ->
      pdesc
  | None ->
      L.(die InternalError) "pdesc_of: no pdesc for %a found" Procname.pp pid


let store_callgraph_as_db program =
  CallGraph.iter_vertex
    (fun pname ->
      let callees = CallGraph.succ program.callgraph pname in
      if not (List.is_empty callees) then Attributes.store_callees pname callees )
    program.callgraph


let all_procs {all_procs} = all_procs

let all_nodes {all_nodes} = all_nodes

let all_instr_nodes {cfgs} =
  Procname.Map.fold
    (fun _ IntraCfg.{pdesc} acc ->
      acc @ (Procdesc.get_nodes pdesc |> List.concat_map ~f:InstrNode.list_of_pnode) )
    cfgs []


let is_library_call t instr_node = InstrNode.Set.mem instr_node t.library_calls

let add_library_call t instr_node = t.library_calls <- InstrNode.Set.add instr_node t.library_calls

let add_entry t proc =
  if not (List.mem t.entries ~equal:Procname.equal proc) then t.entries <- proc :: t.entries


let set_entry t procs = t.entries <- procs

(* let dummy_node = Node.of_pnode (Procdesc.Node.dummy Procname.empty_block) *)

(* let mem_vertex cfgs x = IntraCfg.mem_vertex (cfgof cfgs (Node.get_proc_name x)) x *)

let cg_reachables_of ?(forward = true) ?(reflexive = true) {callgraph} init =
  if Procname.Set.is_empty init then Procname.Set.empty
  else CallGraph.find_reachable_nodes_of ~forward ~reflexive callgraph init


let cfg_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive cfg.graph init


let dom_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive (fst (IntraCfg.get_cfg_dom_tree cfg)) init


let pdom_reachables_of ?(forward = true) ?(reflexive = true) (program : t) (init : NSet.t) : NSet.t
    =
  if NSet.is_empty init then NSet.empty
  else
    let pid = NSet.choose init |> Node.get_proc_name in
    if not (NSet.for_all (fun n -> Procname.equal pid (Node.get_proc_name n)) init) then
      L.progress "[WARNING]: compute cfg_reachables of mutliple procs: %a@." NSet.pp init ;
    let cfg = cfgof program pid in
    IntraCfg.find_reachable_nodes_of ~forward ~reflexive (fst (IntraCfg.get_cfg_pdom_tree cfg)) init


let is_reachable program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.is_reachable (cfgof program pid1) x y else false


let dom program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.dom (cfgof program pid1) x y else false


let pdom program x y =
  let pid1, pid2 = (Node.get_proc_name x, Node.get_proc_name y) in
  if Procname.equal pid1 pid2 then IntraCfg.pdom (cfgof program pid1) x y else false


let is_undef_proc program pid =
  match pdesc_of_opt program pid with
  | Some pdesc ->
      (* NOTE: undefined procedures (e.g., extern) may have a procdesc in Infer IR. *)
      let ProcAttributes.{is_defined} = Procdesc.get_attributes pdesc in
      (not is_defined) || is_builtin_proc pid
  | None ->
      true


let pred program x = IntraCfg.pred (cfgof program (Node.get_proc_name x)) x

let succ program x = IntraCfg.succ (cfgof program (Node.get_proc_name x)) x

let pred_instr_node program x =
  IntraCfg.pred_instr_node (cfgof program (InstrNode.get_proc_name x)) x


let succ_instr_node program x =
  IntraCfg.succ_instr_node (cfgof program (InstrNode.get_proc_name x)) x


let set_side_effects program side_effects = program.side_effects <- side_effects

let side_effects program = program.side_effects

let set_return_values program return_values = program.return_values <- return_values

let return_values program = program.return_values

let is_nonnull_proc program proc =
  match Procname.Map.find_opt proc program.return_values with
  | Some v ->
      AbsConst.is_nonnull v
  | None ->
      false


let is_constant_proc program proc =
  match Procname.Map.find_opt proc program.return_values with
  | Some v ->
      AbsConst.is_constant v
  | None ->
      false


let d4j_build_properties_file = "defects4j.build.properties"

(* let get_blocks cfgs init =
   if NSet.is_empty init then NSet.empty
   else
     let pid = Node.get_proc_name (NSet.choose init) in
     let init = NSet.filter (fun n -> Procname.equal (Node.get_proc_name n) pid) init in
     let is_single_pred n = Int.equal (List.length (pred cfgs n)) 1 in
     let is_single_succ n = Int.equal (List.length (succ cfgs n)) 1 in
     let rec do_worklist acc worklist =
       if NSet.is_empty worklist then acc
       else
         let work = NSet.choose worklist in
         let rest = NSet.remove work worklist in
         let nexts =
           let preds = List.filter (pred cfgs work) ~f:is_single_succ in
           let succs = List.filter (succ cfgs work) ~f:is_single_pred in
           NSet.diff (NSet.of_list (preds @ succs)) acc
         in
         do_worklist (NSet.add work acc) (NSet.union rest nexts)
     in
     do_worklist init init *)

(* FIXME: maybe undefined tenv *)
let _tenv = ref (Tenv.create ())

let tenv () = !_tenv

let original_mpath = Filename.concat Config.sprint_summary_dir "program.data"

let rec build ~do_preanalysis : t =
  let tenv, cfgs =
    let source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
    let procnames =
      List.concat_map source_files ~f:(fun src -> SourceFiles.proc_names_of_source src)
    in
    let tenv = Option.value_exn (Tenv.load_global ()) in
    List.iter source_files ~f:(fun file ->
        let tenv_file =
          try Option.value_exn (Tenv.load file)
          with _ -> L.(die ExternalError "Failed to load tenv file: %a@." SourceFile.pp file)
        in
        Tenv.merge ~src:tenv_file ~dst:tenv ) ;
    let cfgs =
      List.fold procnames ~init:Procname.Map.empty ~f:(fun acc procname ->
          match Procdesc.load procname with
          | Some pdesc ->
              do_preanalysis pdesc ;
              Procname.Map.add procname (IntraCfg.from_pdesc pdesc) acc
          | None ->
              acc )
    in
    (tenv, cfgs)
  in
  let classes = ClassHierachy.create () in
  let calculated_classes = ref Typ.Name.Set.empty in
  let rec collect_class klass =
    if Typ.Name.Set.mem klass !calculated_classes then ()
    else (
      calculated_classes := Typ.Name.Set.add klass !calculated_classes ;
      let superclasses =
        match Tenv.lookup tenv klass with Some Struct.{supers} -> supers | None -> []
      in
      List.iter superclasses ~f:(ClassHierachy.add_edge classes klass) ;
      List.iter superclasses ~f:collect_class )
  in
  List.iter (Tenv.keys tenv) ~f:collect_class ;
  let pdescs = Procname.Map.fold (fun _ IntraCfg.{pdesc} acc -> pdesc :: acc) cfgs [] in
  let program =
    { cfgs
    ; tenv
    ; callgraph= CallGraph.create ()
    ; all_procs= Procname.Map.bindings cfgs |> List.map ~f:fst |> Procname.Set.of_list
    ; all_nodes=
        List.concat_map pdescs ~f:(fun pd ->
            List.map ~f:(InterNode.create (Procdesc.get_proc_name pd)) (Procdesc.get_nodes pd) )
    ; library_calls= InstrNode.Set.empty
    ; field_info= record_field_info tenv cfgs classes
    ; entries= []
    ; class_inits= []
    ; important_param_typs= Procname.Map.empty
    ; classes
    ; return_values= Procname.Map.empty
    ; side_effects= SideEffects.empty }
  in
  print_classhierachy program "class_hierarchy.dot" ;
  program


and record_field_info tenv cfgs classes =
  let field_info = Hashtbl.create 1214 in
  let do_vertex classname =
    let Struct.{fields; statics} = Option.value_exn (Tenv.lookup tenv classname) in
    let static_field_initializers =
      match Procname.Map.find_opt Procname.(Java (Java.get_class_initializer classname)) cfgs with
      | None ->
          (* A class initializer can be None even if the class has static fields.
             Compile-time constant automatically translated into literals *)
          Fieldname.Map.empty
      | Some IntraCfg.{pdesc} ->
          Procdesc.fold_instrs pdesc
            ~f:
              (fun acc _ -> function
                | Sil.Store {e1= Lfield (_, fn, _); e2} ->
                    Fieldname.Map.add fn e2 acc
                | _ ->
                    acc )
            ~init:Fieldname.Map.empty
    in
    let add_field_info ~is_static (fn, typ, annotations) =
      let access_opt =
        List.find_map annotations ~f:(fun (Annot.{class_name}, _) ->
            match class_name with
            | "Default" ->
                Some PredSymb.Default
            | "Private" ->
                Some PredSymb.Private
            | "Protected" ->
                Some PredSymb.Protected
            | "Public" ->
                Some PredSymb.Public
            | _ ->
                None )
      in
      let access =
        match access_opt with
        | Some access ->
            access
        | None ->
            L.debug Capture Quiet "Could not find access anotation from %a.%a@." Typ.Name.pp
              (Fieldname.get_class_name fn) Fieldname.pp fn ;
            PredSymb.Private
      in
      Hashtbl.add field_info fn
        { typ
        ; annotations
        ; access
        ; is_static
        ; is_final= Annot.Item.is_final annotations
        ; initialization= Fieldname.Map.find_opt fn static_field_initializers }
    in
    List.iter fields ~f:(add_field_info ~is_static:false) ;
    List.iter statics ~f:(add_field_info ~is_static:true)
  in
  ClassHierachy.iter_vertex do_vertex classes ;
  field_info


let unique_callee_of_instr_node_opt t instr_node =
  match callees_of_instr_node t instr_node with [callee] -> Some callee | _ -> None


let has_instr ~f node = Instrs.exists (Node.get_instrs node) ~f

let marshalled_path = Filename.concat Config.results_dir "program.data"

let cache : t option ref = ref None

let to_marshal path program =
  cache := Some program ;
  _tenv := program.tenv ;
  Utils.with_file_out path ~f:(fun oc -> Marshal.to_channel oc program [])


let from_marshal ?(do_preanalysis = fun _ -> ()) ?(init = false) () : t =
  match !cache with
  | Some program ->
      _tenv := program.tenv ;
      program
  | None when init ->
      let program = build ~do_preanalysis in
      to_marshal marshalled_path program ;
      cache := Some program ;
      _tenv := program.tenv ;
      program
  | None when Sys.file_exists_exn marshalled_path ->
      let program = Utils.with_file_in marshalled_path ~f:Marshal.from_channel in
      if Config.sprint_launch_spec_inference then to_marshal original_mpath program ;
      cache := Some program ;
      _tenv := program.tenv ;
      program
  | None when Config.sprint_synthesis ->
      let program = build ~do_preanalysis in
      cache := Some program ;
      _tenv := program.tenv ;
      program
  | None ->
      L.(die ExternalError) "Preanalysis has not been executed"


let get_files {cfgs} : SourceFile.t list =
  Procname.Map.fold (fun _ IntraCfg.{file} acc -> file :: acc) cfgs []


let get_nodes program pid =
  let IntraCfg.{pdesc} = cfgof program pid in
  Procdesc.get_nodes pdesc |> List.map ~f:Node.of_pnode


let get_exit_node program pid =
  let pdesc = pdesc_of program pid in
  Node.of_pnode (Procdesc.get_exit_node pdesc)


let get_entry_node program pid =
  let pdesc = pdesc_of program pid in
  Node.of_pnode (Procdesc.get_start_node pdesc)


let get_exit_instr_node program pid =
  let pdesc = pdesc_of program pid in
  Procdesc.get_exit_node pdesc |> InstrNode.list_of_pnode |> List.hd_exn


let get_entry_instr_node program pid =
  let pdesc = pdesc_of program pid in
  Procdesc.get_start_node pdesc |> InstrNode.list_of_pnode |> List.hd_exn


let find_node_with_location {cfgs} (Location.{file; line} as loc) : Node.t list =
  let pdescs = Procname.Map.fold (fun _ IntraCfg.{pdesc} acc -> pdesc :: acc) cfgs [] in
  let pdescs_file_matched =
    List.filter pdescs ~f:(fun pdesc ->
        SourceFile.equal file (Procdesc.get_loc pdesc).Location.file )
  in
  let nodes = List.concat_map pdescs_file_matched ~f:Procdesc.get_nodes in
  let find_nodes_with_line dist =
    match
      List.filter nodes ~f:(fun n ->
          Int.equal (line + dist) (Procdesc.Node.get_loc n).Location.line )
    with
    | [] when dist < 0 ->
        L.debug L.Analysis L.Quiet
          "[Program] Could not find nodes at location even within +- range 1 for %a@."
          Location.pp_file_pos loc ;
        None
    | [] ->
        None
    | nodes ->
        if not (Int.equal dist 0) then
          L.debug L.Analysis L.Quiet "[Program] Nodes were not at line %d but distance %d@." line
            dist ;
        Some (List.map nodes ~f:Node.of_pnode)
  in
  match List.find_map [0; 1; -1] ~f:find_nodes_with_line with Some nodes -> nodes | None -> []


module TypSet = Caml.Set.Make (Typ)

let fields_of_typ program Typ.{desc} =
  match desc with
  | Tstruct strname -> (
    match Tenv.lookup program.tenv strname with Some {fields} -> fields | None -> [] )
  | _ ->
      []


let rec subtyps_of program typ =
  let fields = fields_of_typ program typ in
  List.fold fields ~init:TypSet.empty ~f:(fun acc (_, typ', _) ->
      TypSet.union (subtyps_of program typ') acc )


let is_primitive_type Typ.{desc} = match desc with Tint _ | Tfloat _ | Tfun -> true | _ -> false

let is_consistent_type t1 t2 =
  if Typ.is_pointer_to_void t1 || Typ.is_pointer_to_void t2 then true
  else if is_primitive_type t1 && is_primitive_type t2 then true
  else
    match (t1.Typ.desc, t2.Typ.desc) with
    | Tfun, Tfun ->
        true
    | Tvoid, Tvoid ->
        true
    | Tptr _, Tptr _ ->
        true
    | Tstruct _, Tstruct _ ->
        true
    | Tarray _, Tarray _ ->
        true
    | Tarray _, Tstruct _ | Tstruct _, Tarray _ ->
        true
    | _ ->
        false


let rec type_hierachy program t1 t2 : three_value =
  (* NOTE: we will ignore pointer in Java *)
  match (t1.Typ.desc, t2.Typ.desc) with
  | t1_desc, t2_desc when Typ.equal_desc t1_desc t2_desc ->
      `Yes
  | _ when Typ.is_pointer_to_void t2 ->
      `Yes
  | Tvoid, _ ->
      `Yes (* dynamic type *)
  | _ -> (
      let t1, t2 = (unwrap_if_pointer t1, unwrap_if_pointer t2) in
      match (t1.Typ.desc, t2.Typ.desc) with
      | _ when not (is_consistent_type t1 t2) ->
          `No
      | Tint _, Tint _ | Tfloat _, Tfloat _ ->
          `Yes
      | Tint _, Tfloat _ | Tfloat _, Tint _ ->
          (* allow implicity type conversion *)
          `Yes
      | Tptr (t1', Typ.Pk_pointer), Tptr (t2', Typ.Pk_pointer) ->
          type_hierachy program t1' t2'
      | Tptr _, Tptr _ ->
          `Unknown (* TODO: C++ reference *)
      | Tstruct (CStruct _), Tstruct (CStruct _) ->
          (* TODO: C struct *)
          `Unknown
      | Tstruct (JavaClass _ as name1), Tstruct (JavaClass _ as name2) -> (
        match Subtype.check_subtype program.tenv name1 name2 with
        | _ when Typ.Name.equal Typ.Name.Java.java_lang_object name2 ->
            (* for byte-generated class; they have no class hierachy information *)
            `Yes
        | Subtype.Yes ->
            `Yes
        | Subtype.No ->
            `No
        | Subtype.Unknown ->
            `Unknown )
      | Tarray _, Tstruct name when Typ.Name.equal name Typ.Name.Java.java_lang_object ->
          `Yes
      | Tarray _, Tstruct _ ->
          `No
      | Tstruct _, Tarray _ ->
          `No
      | Tstruct _, Tstruct _ ->
          (* TODO: CUnion, C++ class *)
          `Unknown
      | _ ->
          `Unknown )


let has_annot program annot pid =
  let pdesc = pdesc_of program pid in
  let method_annotation = (Procdesc.get_attributes pdesc).ProcAttributes.method_annotation in
  let annot_return = method_annotation.return in
  Annotations.ia_ends_with annot_return annot


let resolve_method class_name proc =
  let method_exists proc procs = List.mem procs proc ~equal:Procname.equal in
  Tenv.resolve_method ~method_exists !_tenv class_name proc


let slice_virtual_calls program executed_procs trace_procs =
  let reachable_callees = cg_reachables_of program ~forward:true ~reflexive:true executed_procs in
  Procname.Set.iter
    (fun proc ->
      if not (Procname.Set.mem proc reachable_callees) then
        CallGraph.remove_vertex program.callgraph proc )
    reachable_callees ;
  Procname.Set.iter
    (fun proc ->
      match pdesc_of_opt program proc with
      | Some pdesc ->
          let instr_nodes =
            Procdesc.get_nodes pdesc |> List.concat_map ~f:InstrNode.list_of_pnode
          in
          List.iter instr_nodes ~f:(fun instr_node ->
              let proc = InstrNode.get_proc_name instr_node in
              let callees = callees_of_instr_node program instr_node in
              if List.length callees > 1 then
                let inter_callees =
                  Procname.Set.inter trace_procs (Procname.Set.of_list callees)
                  |> Procname.Set.elements
                in
                match inter_callees with
                | [_] ->
                    ()
                | _ ->
                    List.iter callees ~f:(fun callee ->
                        CallGraph.remove_edge_e program.callgraph (proc, instr_node, callee) ) )
      | None ->
          () )
    executed_procs


let methods_in_class ?(find_library_methods = false) program cls =
  let procnames =
    if find_library_methods then
      match Tenv.lookup (tenv ()) cls with
      | Some {methods} ->
          Procname.Set.of_list methods
      | _ ->
          all_procs program
    else all_procs program
  in
  Procname.Set.fold
    (fun procname acc ->
      match Procname.get_class_type_name procname with
      | Some typ when Typ.Name.equal cls typ ->
          Procname.Set.add procname acc
      | Some typ ->
          (* L.progress "%a(%a) is different from %a@." Typ.Name.pp typ Procname.pp procname Typ.Name.pp cls ; *)
          acc
      | None ->
          (* L.progress "%a is not java method of %a@." Procname.pp procname Typ.Name.pp cls ; *)
          acc )
    procnames Procname.Set.empty


let find_methods_in_class ?(find_library_methods = false) ?(pred = fun _ -> true) program cls =
  let module SSet = PrettyPrintable.MakePPSet (String) in
  let rec __find_methods_in_class program cls collected_method_signatures ~pred =
    let dummy_type_name = Typ.Name.Java.from_string "FL4APR_DUMMY_TYPE_NAME" in
    let get_method_signature procname =
      Procname.to_simplified_string ~withclass:false
        (Procname.replace_class procname dummy_type_name)
    in
    let methods = methods_in_class program cls ~find_library_methods in
    let collected_methods =
      Procname.Set.filter
        (fun procname ->
          (not (SSet.mem (get_method_signature procname) collected_method_signatures))
          && pred procname )
        methods
    in
    match Tenv.lookup (tenv ()) cls with
    | _ when String.is_suffix (Typ.Name.to_string cls) ~suffix:".TestCase" ->
        collected_methods
    | Some Struct.{supers} ->
        let method_signatures_accum =
          Procname.Set.fold
            (fun procname acc -> SSet.add (get_method_signature procname) acc)
            collected_methods collected_method_signatures
        in
        List.fold supers ~init:collected_methods ~f:(fun acc super ->
            Procname.Set.union acc
              (__find_methods_in_class program super method_signatures_accum ~pred) )
    | _ ->
        collected_methods
  in
  __find_methods_in_class program cls SSet.empty ~pred


let executed_by_jvm program proc =
  match proc with
  | Procname.Java mthd when is_entry program proc ->
      let cls = Procname.Java.get_class_type_name mthd in
      let procs = methods_in_class program cls in
      let clinit =
        Procname.Set.filter (fun proc -> Procname.get_method proc |> String.equal "<clinit>") procs
      in
      let init =
        Procname.Set.filter (fun proc -> Procname.get_method proc |> String.equal "<init>") procs
      in
      let junit_models = find_methods_in_class program cls ~pred:JunitModel.is_model in
      L.progress "Junit Model methods of %a:@.%a@." Procname.pp proc Procname.Set.pp junit_models ;
      Procname.Set.union clinit junit_models |> Procname.Set.union init
  | Procname.Java mthd ->
      let cls = Procname.Java.get_class_type_name mthd in
      let procs = methods_in_class program cls in
      let clinit =
        Procname.Set.filter (fun proc -> Procname.get_method proc |> String.equal "<clinit>") procs
      in
      clinit
  | _ ->
      Procname.Set.empty


let slice_procs_except ({callgraph} as program) procs =
  (* TODO: collect recursively executed methods
     let rec __executed_by_jvm acc =
       let next = Procname.Set.fold (fun proc -> Procname.Set.union (executed_by_jvm program proc)) acc acc in
       if Int.equal (Procname.Set.cardinal next) (Procname.Set.cardinal acc) then acc else __executed_by_jvm next
     in *)
  let procs =
    Procname.Set.fold (fun proc -> Procname.Set.union (executed_by_jvm program proc)) procs procs
  in
  let to_remove =
    CallGraph.fold_vertex
      (fun proc acc -> if Procname.Set.mem proc procs then acc else Procname.Set.add proc acc)
      callgraph Procname.Set.empty
  in
  Procname.Set.iter
    (fun to_remove ->
      program.cfgs <- Procname.Map.remove to_remove program.cfgs ;
      CallGraph.remove_vertex callgraph to_remove )
    to_remove


let is_sliced_method {cfgs} proc = not (Procname.Map.mem proc cfgs)

let remove_cfg_if_no_cg program =
  let program =
    Procname.Set.fold
      (fun proc acc ->
        if CallGraph.mem_vertex program.callgraph proc then acc
        else
          { program with
            cfgs= Procname.Map.remove proc acc.cfgs
          ; all_procs= Procname.Set.remove proc acc.all_procs } )
      (all_procs program) program
  in
  print_to_file ~dirname:(Some Config.results_dir) ~filename:"sliced_procs"
    ~msg:
      (F.asprintf "Sliced Procs:@. %a@.=======================@." (Pp.seq Procname.pp ~sep:"\n")
         (Procname.Map.bindings program.cfgs |> List.map ~f:fst) ) ;
  program


let _junit_node = ref Procname.Map.empty

let compute_node_for_junit_premethods program ?(pdesc_opt = None) ~clinits baseClass proc =
  let dummy = Procdesc.Node.dummy proc in
  (* targetTest(this) {
          Test.beforeClass();
          this = __new();
          this.<init>();
          this.setUp();
     } *)
  let pdesc = match pdesc_opt with Some pdesc -> pdesc | None -> pdesc_of program proc in
  let this_var, this_typ = Procdesc.get_pvar_formals pdesc |> List.hd_exn in
  let procs_baseClass = methods_in_class program baseClass in
  let cls_typ = Typ.mk_struct baseClass in
  let inits =
    Procname.Set.filter
      (fun proc -> Procname.get_method proc |> String.equal "<init>")
      procs_baseClass
  in
  if Procname.Set.is_empty inits then
    L.(die InternalError)
      "could not find init methods for %a, %a" Typ.Name.pp baseClass Procname.pp proc ;
  let before_classes = find_methods_in_class program baseClass ~pred:JunitModel.is_before_class in
  let before_methods = find_methods_in_class program baseClass ~pred:JunitModel.is_before in
  let loc = Procdesc.get_loc pdesc in
  let clinit_instrs =
    Procname.Set.fold
      (fun proc acc ->
        Sil.Call ((Ident.create_none (), Typ.void), Const (Cfun proc), [], loc, CallFlags.default)
        :: acc )
      clinits []
  in
  let before_class_instrs =
    List.map (Procname.Set.elements before_classes) ~f:(fun bc ->
        Sil.Call ((Ident.create_none (), Typ.void), Const (Cfun bc), [], loc, CallFlags.default) )
  in
  let init_instrs =
    let ret_id = Ident.create_fresh Ident.knormal in
    let init = Procname.Set.choose inits in
    let call_instr =
      match Procdesc.get_formals (pdesc_of program init) with
      | [(_, _)] ->
          Sil.Call
            ( (ret_id, Typ.void)
            , Const (Cfun init)
            , [(Exp.Var ret_id, this_typ)]
            , loc
            , CallFlags.default )
      | [(_, _); (_, arg_typ)] when Typ.equal arg_typ Typ.pointer_to_java_lang_string ->
          Sil.Call
            ( (ret_id, Typ.void)
            , Const (Cfun init)
            , [(Exp.Var ret_id, this_typ); (Exp.Const (Cstr ""), arg_typ)]
            , loc
            , CallFlags.default )
      | _ ->
          L.(die ExternalError) "%a has multiple parameters" Procname.pp init
    in
    let before_method_instrs =
      List.map (Procname.Set.elements before_methods) ~f:(fun bm ->
          Sil.Call
            ( (Ident.create_none (), Typ.void)
            , Const (Cfun bm)
            , [(Exp.Var ret_id, this_typ)]
            , loc
            , CallFlags.default ) )
    in
    clinit_instrs
    @ [ Sil.Call
          ( (ret_id, this_typ)
          , Const (Cfun BuiltinDecl.__new)
          , [ ( Exp.Sizeof
                  {typ= cls_typ; nbytes= None; dynamic_length= None; subtype= Subtype.subtypes}
              , Typ.void ) ]
          , loc
          , CallFlags.default )
      ; Sil.Store {e1= Exp.Lvar this_var; root_typ= cls_typ; typ= this_typ; e2= Exp.Var ret_id; loc}
      ; call_instr ]
    @ before_method_instrs
  in
  let instrs = before_class_instrs @ init_instrs in
  L.debug L.Analysis L.Quiet "inserted junit methods for (%a, %a):@. - %a@." Typ.Name.pp baseClass
    Procname.pp proc (Pp.seq ~sep:"\n - " pp_instr) instrs ;
  Procdesc.Node.replace_instrs_with_given dummy (Instrs.of_list instrs) ;
  dummy


let node_for_junit_premethods program ?(pdesc_opt = None) ~clinits baseClass proc =
  match Procname.Map.find_opt proc !_junit_node with
  | Some cls_map -> (
    match Typ.Name.Map.find_opt baseClass cls_map with
    | Some junit_node ->
        junit_node
    | None ->
        let junit_node =
          compute_node_for_junit_premethods program ~pdesc_opt ~clinits baseClass proc
        in
        let cls_map = Typ.Name.Map.add baseClass junit_node cls_map in
        _junit_node := Procname.Map.add proc cls_map !_junit_node ;
        junit_node )
  | None ->
      let junit_node =
        compute_node_for_junit_premethods program ~pdesc_opt ~clinits baseClass proc
      in
      let cls_map = Typ.Name.Map.add baseClass junit_node Typ.Name.Map.empty in
      _junit_node := Procname.Map.add proc cls_map !_junit_node ;
      junit_node


let get_expected_exn_typ program test_method =
  let pdesc = pdesc_of program test_method in
  let proc_attrs = Procdesc.get_attributes pdesc in
  let method_annot = ProcAttributes.(proc_attrs.method_annotation) in
  let open Annot in
  List.find_map
    Method.(method_annot.return :: method_annot.params)
    ~f:(fun item ->
      List.find_map item ~f:(fun (annot, _) ->
          match find_parameter annot ~name:"expected" with
          | Some (Class typ) ->
              Some typ
          | _ ->
              None ) )


let get_failing_test_methods program =
  List.fold Config.sprint_test_methods ~init:[] ~f:(fun acc qualified_method_name ->
      L.debug L.Analysis L.Quiet "parse %s@." qualified_method_name ;
      let[@warning "-8"] [classpath; _; method_name] = String.split qualified_method_name ~on:':' in
      let klass = Typ.Name.Java.from_string classpath in
      let found =
        find_methods_in_class program klass ~pred:(fun procname ->
            String.( = ) method_name (Procname.get_method procname) )
      in
      match Procname.Set.is_singleton_or_more found with
      | Empty ->
          L.(die ExternalError) "There is no method %s in captured methods" qualified_method_name
      | More ->
          L.(die ExternalError)
            "There are multiple methods matched with %s: %a@." qualified_method_name Procname.Set.pp
            found
      | Singleton method_with_body ->
          (klass, method_with_body) :: acc )


let all_pvars_of program procname =
  let pdesc = pdesc_of program procname in
  let local_pvars =
    Procdesc.get_locals pdesc
    |> List.map ~f:(fun ProcAttributes.{name; typ} -> (Pvar.mk name procname, typ))
  in
  let formal_pvars = Procdesc.get_pvar_formals pdesc in
  let return_var_typ = (Procdesc.get_ret_var pdesc, Procdesc.get_ret_type pdesc) in
  (return_var_typ :: local_pvars) @ formal_pvars


let is_float typ = match Typ.(typ.desc) with Typ.Tfloat _ -> true | _ -> false

let all_classes {classes} =
  ClassHierachy.fold_vertex Typ.Name.Set.add classes Typ.Name.Set.empty |> Typ.Name.Set.elements


let model_field_map =
  let add_model cls_str fld_str typ = Fieldname.Map.add (make_field cls_str fld_str) typ in
  Fieldname.Map.empty
  |> add_model "java.lang.StringBuilder" "value" (Typ.mk_struct Typ.Name.Java.java_lang_string)
  |> Fieldname.Map.add mElementsField (Typ.mk_struct Typ.Name.Java.java_lang_object)
  |> Fieldname.Map.add mIsEmptyField Typ.int
  |> Fieldname.Map.add mConcurrentField (Typ.mk_struct Typ.Name.Java.java_lang_object)
  |> Fieldname.Map.add mKeysField (Typ.mk_struct Typ.Name.Java.java_lang_object)
  |> Fieldname.Map.add mValuesField (Typ.mk_struct Typ.Name.Java.java_lang_object)
  |> add_model "javax.swing.event.EventListenerList" "mListenerList"
       (strip_ptr Typ.pointer_to_java_lang_object)


let _field_typ_map = ref model_field_map

let get_field_typ_opt fn =
  match Fieldname.Map.find_opt fn !_field_typ_map with
  | Some typ ->
      Some typ
  | None -> (
      let lookup = Tenv.lookup (tenv ()) in
      let parent_typ = Typ.mk_struct (Fieldname.get_class_name fn) in
      match Struct.get_field_type_and_annotation ~lookup fn parent_typ with
      | Some (typ, _) ->
          _field_typ_map := Fieldname.Map.add fn typ !_field_typ_map ;
          Some typ
      | None ->
          None )


let compute_pv_typ_map proc =
  let pdesc = pdesc_of (from_marshal ()) proc in
  let init = Var.Map.empty in
  let init =
    List.fold (Procdesc.get_pvar_formals pdesc) ~init ~f:(fun acc (pv, typ) ->
        Var.Map.add (Var.of_pvar pv) typ acc )
  in
  let ProcAttributes.{locals} = Procdesc.get_attributes pdesc in
  let results =
    List.fold locals ~init ~f:(fun acc ProcAttributes.{name; typ} ->
        if Typ.is_void typ then
          (* L.user_warning "%a is ill-typed variable@." Mangled.pp name ; *)
          acc
        else Var.Map.add (Var.of_pvar (Pvar.mk name proc)) typ acc )
  in
  let ret_var = Procdesc.get_ret_var pdesc |> Var.of_pvar in
  match proc with
  | Procname.Java mthd ->
      Var.Map.add ret_var (Procname.Java.get_return_typ mthd) results
  | _ ->
      Var.Map.add ret_var (Procdesc.get_ret_type pdesc) results


let _pv_typ_map = ref Procname.Map.empty

let get_pvar_typ_opt pv =
  match Pvar.get_declaring_function pv with
  | Some proc -> (
    match Procname.Map.find_opt proc !_pv_typ_map with
    | Some pv_typ_map ->
        Var.Map.find_opt (Var.of_pvar pv) pv_typ_map
    | None ->
        let pv_typ_map = compute_pv_typ_map proc in
        _pv_typ_map := Procname.Map.add proc pv_typ_map !_pv_typ_map ;
        Var.Map.find_opt (Var.of_pvar pv) pv_typ_map )
  | None ->
      None


let _recursive = ref Procname.Map.empty

let is_self_recursive proc =
  let program = from_marshal () in
  let callees = callees_of_proc program proc in
  List.mem callees proc ~equal:Procname.equal


let is_recursive program proc =
  match Procname.Map.find_opt proc !_recursive with
  | Some bool ->
      bool
  | None ->
      let callees =
        cg_reachables_of ~forward:true ~reflexive:false program (Procname.Set.singleton proc)
      in
      let result = Procname.Set.mem proc callees in
      _recursive := Procname.Map.add proc result !_recursive ;
      result


let find_recursive procs =
  let program = from_marshal () in
  Procname.Set.iter
    (fun proc ->
      let callees = callees_of_proc program proc in
      let recur_callees =
        List.filter
          ~f:(fun callee ->
            Procname.Set.mem proc (callees_of_proc program callee |> Procname.Set.of_list) )
          callees
      in
      L.progress "recursive procs of %a: %a@." Procname.pp proc (Pp.seq Procname.pp ~sep:"\n")
        recur_callees )
    procs


module PreProcCg = struct
  module Node = struct
    type t = Procname.t

    type id = string

    let id proc = F.asprintf "%a" Procname.pp proc

    module IdMap = PrettyPrintable.MakePPMap (String)
  end

  type t = CallGraph.t

  let fold_succs g =
    let fold n ~init ~f =
      let fold_fun proc acc = f acc proc in
      CallGraph.fold_succ fold_fun g n init
    in
    fold


  let start_node g = Procname.from_string_c_fun "CallStart"
end

module WTO = WeakTopologicalOrder.Bourdoncle_SCC (PreProcCg)

let wto_cg program target_procs =
  let cg = CallGraph.create () in
  let start_node = PreProcCg.start_node cg in
  CallGraph.iter_edges_e
    (fun (caller, callnode, callee) ->
      if
        is_undef_proc program callee |> not
        && Procname.Set.mem callee target_procs
        && Procname.Set.mem caller target_procs
      then CallGraph.add_edge_e cg (callee, callnode, caller) )
    program.callgraph ;
  if CallGraph.is_empty cg then CallGraph.add_edge_e cg (start_node, InstrNode.dummy, start_node) ;
  print_callgraph {program with callgraph= cg} "target_cg.dot" ;
  CallGraph.iter_vertex
    (fun proc -> CallGraph.add_edge_e cg (start_node, InstrNode.dummy_of_proc start_node, proc))
    cg ;
  WTO.make cg


let _callback_fields = ref None

let collect_callback_fields program =
  match !_callback_fields with
  | Some fields ->
      fields
  | None ->
      let all_classes = all_classes program in
      let fields =
        List.fold all_classes ~init:Fieldname.Set.empty ~f:(fun acc klass ->
            match Tenv.lookup (tenv ()) klass with
            | Some {fields; statics} ->
                List.fold (fields @ statics) ~init:acc ~f:(fun acc (fn, _, _) ->
                    (* if pred fn then *)
                    if String.is_suffix (Fieldname.to_simplified_string fn) ~suffix:"callback" then
                      Fieldname.Set.add fn acc
                    else acc )
            | None ->
                acc )
        |> Fieldname.Set.elements
      in
      _callback_fields := Some fields ;
      fields


let callee_dispatch ~base_class ~is_exact mthd =
  let program = from_marshal () in
  let init = base_class |> Typ.Name.Set.singleton in
  let classes_candidates =
    if is_exact then Typ.Name.Set.elements init
    else
      ClassHierachy.find_reachable_nodes_of program.classes ~forward:false ~reflexive:true init
      |> Typ.Name.Set.elements
  in
  let callees =
    let method_exists proc procs = List.mem procs proc ~equal:Procname.equal in
    List.filter_map classes_candidates ~f:(fun class_name ->
        Tenv.resolve_method ~method_exists program.tenv class_name (Procname.Java mthd) )
    |> Procname.Set.of_list
  in
  callees


let construct_cg program =
  Procname.Map.iter
    (fun proc_name _ ->
      match proc_name with
      | Procname.Java mthd ->
          let class_type = Procname.Java.get_class_type_name mthd in
          let superclasses =
            match Tenv.lookup program.tenv class_type with
            | Some Struct.{supers} ->
                supers
            | None ->
                []
          in
          List.iter superclasses ~f:(fun supercls ->
              ClassHierachy.add_edge program.classes class_type supercls )
      | _ ->
          () )
    program.cfgs ;
  let library_calls =
    Procname.Map.fold
      (fun _ IntraCfg.{pdesc} acc ->
        let instr_nodes =
          Procdesc.get_nodes pdesc
          |> List.concat_map ~f:InstrNode.list_of_pnode
          |> List.filter ~f:InstrNode.is_call_node
        in
        List.fold instr_nodes ~init:acc ~f:(fun acc instr_node ->
            let callees =
              let instr = InstrNode.get_instr instr_node in
              match instr with
              | Sil.Call (_, Const (Cfun (Procname.Java mthd)), _, _, {cf_virtual}) when cf_virtual
                ->
                  callee_dispatch
                    ~base_class:(Procname.Java.get_class_type_name mthd)
                    ~is_exact:false mthd
                  |> Procname.Set.elements
              | Sil.Call (_, Const (Cfun callee), _, _, _) ->
                  [callee]
              | _ ->
                  []
            in
            let _, callees_defed = List.partition_tf callees ~f:(is_undef_proc program) in
            List.iter callees ~f:(add_call_edge program instr_node) ;
            if List.is_empty callees_defed then InstrNode.Set.add instr_node acc else acc ) )
      program.cfgs InstrNode.Set.empty
  in
  print_callgraph program "callgraph.dot" ;
  print_to_file ~dirname:None
    ~msg:(F.asprintf "%a" InstrNode.Set.pp library_calls)
    ~filename:"library_calls" ;
  {program with library_calls}


let array_length_field =
  Fieldname.make (Typ.Name.Java.from_string "java.lang.reflect.Array") "length"


let get_fieldinfo {field_info} fn =
  match Hashtbl.find_opt field_info fn with
  | Some info ->
      info
  | None when Fieldname.equal fn array_length_field ->
      let info =
        { typ= Typ.int
        ; annotations= [(Annot.final, true)]
        ; is_static= false
        ; access= PredSymb.Public
        ; is_final= false
        ; initialization= None }
      in
      Hashtbl.add field_info fn info ;
      info
  | None ->
      let Struct.{typ; annotations; is_static} =
        Option.value_exn
          (Struct.get_field_info
             ~lookup:(Tenv.lookup (tenv ()))
             fn
             (Typ.mk_struct (Fieldname.get_class_name fn)) )
      in
      let info =
        { typ
        ; annotations
        ; is_static
        ; access= PredSymb.Private
        ; is_final= false
        ; initialization= None }
      in
      Hashtbl.add field_info fn info ;
      info


let find_overloaded_methods program mthd =
  let name = Procname.Java.get_method mthd in
  let ret_type = Procname.Java.get_return_typ mthd in
  methods_in_class ~find_library_methods:true program (Procname.Java.get_class_type_name mthd)
  |> Procname.Set.elements
  |> List.map ~f:(Procname.as_java_exn ~explanation:"")
  |> List.filter ~f:(fun m ->
         (not (Procname.equal (Java mthd) (Java m)))
         && String.equal (Procname.Java.get_method m) name
         && Typ.equal ret_type (Procname.Java.get_return_typ m) )


module Class = struct
  type klass = Typ.name

  module G = ClassHierachy

  let test_classes =
    match Utils.read_file (Config.project_root ^/ Config.d4j_all_tests_file) with
    | Result.Ok class_names ->
        List.map class_names ~f:Typ.Name.Java.from_string
    | _ ->
        []


  let is_testclass_str classpath =
    match String.rsplit2 classpath ~on:'.' with
    | _
      when String.is_suffix classpath ~suffix:"Test"
           || String.is_suffix classpath ~suffix:"Tests"
           || String.is_suffix classpath ~suffix:"TestCase" ->
        true
    | Some (_, classpath) ->
        String.is_prefix classpath ~prefix:"Test"
    | None ->
        false


  let rec outermost_class_of klass =
    let jclass = Typ.Name.Java.get_java_class_name_exn klass in
    match JavaClassName.get_outer_class_name jclass with
    | Some outer_name ->
        let outer_klass = Typ.Name.Java.from_string (JavaClassName.to_string outer_name) in
        outermost_class_of outer_klass
    | None ->
        klass


  let is_testclass klass = outermost_class_of klass |> Typ.Name.name |> is_testclass_str

  let has_child {classes} klass = G.pred classes klass |> List.is_empty |> not

  let find_all_children {classes} ~reflexive klass =
    G.find_reachable_nodes_of classes ~forward:false ~reflexive (Typ.Name.Set.singleton klass)
    |> Typ.Name.Set.elements


  let find_impl ({tenv} as pgm) interface =
    List.filter (find_all_children ~reflexive:false pgm interface) ~f:(fun child ->
        match Tenv.lookup tenv child with
        | Some child_info when Struct.is_not_java_interface child_info ->
            true
        | _ ->
            false )


  let find_siblings {classes} klass =
    match G.succ classes klass with
    | [super] when not (Typ.Name.equal super Typ.Name.Java.java_lang_object) ->
        snd (List.partition_tf (G.pred classes super) ~f:(Typ.Name.equal klass))
    | _ ->
        []


  let lookup {tenv} klass = Tenv.lookup tenv klass

  let is_interface t klass =
    match lookup t klass with
    | Some Struct.{java_class_info= Some {kind}} ->
        Struct.equal_java_class_kind kind Struct.Interface
    | _ ->
        false


  let is_abstract t klass =
    match lookup t klass with
    | Some Struct.{java_class_info= Some {kind}} ->
        Struct.equal_java_class_kind kind Struct.AbstractClass
    | _ ->
        false


  let enum = Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Enum")

  let is_enum t klass =
    match type_hierachy t (Typ.mk_struct klass) enum with `Yes -> true | _ -> false


  let is_abstract t klass =
    match lookup t klass with
    | Some Struct.{java_class_info= Some {kind}} ->
        Struct.equal_java_class_kind kind Struct.AbstractClass
    | _ ->
        false


  let is_test_class = List.mem ~equal:Typ.Name.equal test_classes
end

let is_interface_or_abstract_class_typ typ =
  let program = from_marshal () in
  match unwrap_if_pointer typ with
  | Typ.{desc= Tstruct name} ->
      Class.is_interface program name || Class.is_abstract program name
  | _ ->
      false


(* let _innerclass_field_cache = ref Fieldname.Map.empty *)

let is_innerclass_field fn =
  (* match Fieldname.Map.find_opt fn !_innerclass_field_cache with
     | Some b ->
         b
     | None -> *)
  let class_name = Fieldname.get_class_name fn in
  let result =
    match
      (Tenv.lookup (tenv ()) class_name, Typ.Name.Java.is_anonymous_inner_class_name_opt class_name)
    with
    | _, Some true ->
        false
    | Some Struct.{static}, _ ->
        (not static) && String.contains (Typ.Name.to_string class_name) '$'
    | None, _ ->
        false
  in
  (* _innerclass_field_cache := Fieldname.Map.add fn result !_innerclass_field_cache ; *)
  result


module CFG = struct
  module G = IntraCfg.G

  module Dot = Graph.Graphviz.Dot (struct
    include G

    let graph_attributes _ = []

    let default_vertex_attributes _ = []

    let vertex_name v = F.asprintf "%a" Procdesc.Node.pp (InterNode.pnode_of v)

    let vertex_attributes _ = []

    let get_subgraph _ = None

    let default_edge_attributes _ = []

    let edge_attributes _ = []
  end)

  let print_to_dot program procname ~path =
    let cfg = Procname.Map.find procname program.cfgs in
    Utils.with_file_out path ~f:(fun oc -> Dot.output_graph oc cfg.graph)


  let find_outer_block_node program node =
    let rec last_node_of_same_block n =
      match InterNode.get_succs n with [succ] -> last_node_of_same_block succ | _ -> n
    in
    let pdom_cands =
      last_node_of_same_block node |> NSet.singleton
      |> cfg_reachables_of ~forward:true ~reflexive:false program
      |> NSet.elements
    in
    let post_dominators =
      List.filter pdom_cands ~f:(fun n -> (not (dom program node n)) && pdom program n node)
    in
    match
      List.filter post_dominators ~f:(fun pd ->
          List.for_all post_dominators ~f:(fun n -> pdom program n pd) && not (Node.equal pd node) )
    with
    | [n] ->
        Some n
    | _ ->
        None


  let switch_locs_tbl : (SourceFile.t, Location.t list) Hashtbl.t = Hashtbl.create 1214

  let rec is_switch_location (Location.{file} as loc) =
    match Hashtbl.find_opt switch_locs_tbl file with
    | Some locations ->
        List.mem locations loc ~equal:Location.equal
    | None ->
        ( match Utils.read_file (SourceFile.to_rel_path file) with
        | Ok lines ->
            List.filter_mapi
              ~f:(fun i line ->
                Option.some_if
                  (Str.string_match (Str.regexp ".* switch (.+)") line 0)
                  {loc with line= i + 1} )
              lines
        | _ ->
            [] )
        |> Hashtbl.add switch_locs_tbl file ;
        is_switch_location loc
end

let find_equals_proc (typ : Typ.t) =
  let program = from_marshal () in
  let tenv = program.tenv in
  let visited = ref Typ.Name.Set.empty in
  let rec resolve_name_struct (class_name : Typ.Name.t) (class_struct : Struct.t) =
    if
      (not (Typ.Name.is_class class_name))
      || (not (Struct.is_not_java_interface class_struct))
      || Typ.Name.Set.mem class_name !visited
    then None
    else (
      visited := Typ.Name.Set.add class_name !visited ;
      match List.find class_struct.methods ~f:(String.equal "equals" <<< Procname.get_method) with
      | Some proc when not (is_undef_proc program proc) ->
          L.d_printfln "find equals in %a" Typ.Name.pp class_name ;
          Some proc
      | _ ->
          L.d_printfln "could not find equals in %a" Typ.Name.pp class_name ;
          List.find_map class_struct.supers ~f:resolve_name )
  and resolve_name class_name =
    Tenv.lookup tenv class_name |> Option.bind ~f:(resolve_name_struct class_name)
  in
  match typ.desc with Tstruct class_name -> resolve_name class_name | _ -> None


let is_nonnull_static_final_field field =
  let program = from_marshal () in
  try
    let fieldinfo = get_fieldinfo program field in
    match fieldinfo with
    | {is_static; is_final; initialization= Some exp} ->
        is_static && is_final && not (Exp.is_null_literal exp)
    | {is_static; is_final; initialization= None} ->
        (* unsound heuristics *)
        is_static && is_final
  with _ -> true


let find_common_superclasses lhs rhs =
  let program = from_marshal () in
  let super_lhs, super_rhs =
    ( ClassHierachy.find_reachable_nodes_of ~reflexive:true program.classes
        (Typ.Name.Set.singleton lhs)
    , ClassHierachy.find_reachable_nodes_of ~reflexive:true program.classes
        (Typ.Name.Set.singleton rhs) )
  in
  Typ.Name.Set.inter super_lhs super_rhs


let has_nontrivial_common_parent lhs rhs =
  let common_parents = find_common_superclasses lhs rhs in
  let result = Typ.Name.Set.exists (Typ.Name.equal Typ.Name.Java.java_lang_object) common_parents in
  L.d_printfln "%a and %a has common parent!" Typ.Name.pp lhs Typ.Name.pp rhs ;
  result


let has_recursive_field name =
  match Tenv.lookup (tenv ()) name with
  | Some Struct.{fields} ->
      List.exists fields ~f:(fun (_, typ, _) ->
          match strip_ptr typ with
          | Typ.{desc= Tstruct name'} ->
              Typ.Name.equal name name'
          | _ ->
              false )
  | None ->
      false


let __fieldname_getter = ref Fieldname.Map.empty

let compute_getter_field proc =
  let program = from_marshal () in
  let pdesc = pdesc_of program proc in
  let nodes = Procdesc.get_nodes pdesc in
  match List.filter nodes ~f:is_retnode with
  | [node] -> (
      let instrs = get_instrs_list node in
      match instrs with
      | Sil.Load {e= Exp.Lvar this_pv}
        :: Sil.Load {e= Exp.Lfield (_, fn, _)}
        :: Sil.Store {e1= Exp.Lvar ret_pv}
        :: _
        when Pvar.is_this this_pv && Pvar.is_return ret_pv ->
          L.progress " - * * found getter field %a@." Fieldname.pp fn ;
          Some fn
      | _ ->
          None )
  | _ ->
      None


let rec has_syntactic_getter fieldname =
  match Fieldname.Map.find_opt fieldname !__fieldname_getter with
  | Some result ->
      result
  | None -> (
      let program = from_marshal () in
      let cls = Fieldname.get_class_name fieldname in
      let procs = methods_in_class ~find_library_methods:false program cls in
      let fieldnames_with_getter =
        List.filter_map (Procname.Set.elements procs) ~f:compute_getter_field
      in
      match Tenv.lookup (tenv ()) cls with
      | Some Struct.{fields; statics} -> (
          let all_fields = List.map (fields @ statics) ~f:(fun (fn, _, _) -> fn) in
          List.iter all_fields ~f:(fun fn ->
              if List.mem fieldnames_with_getter ~equal:Fieldname.equal fn then
                __fieldname_getter := Fieldname.Map.add fn true !__fieldname_getter
              else if Typ.Name.equal cls (Fieldname.get_class_name fn) then
                __fieldname_getter := Fieldname.Map.add fn false !__fieldname_getter ) ;
          match Fieldname.Map.find_opt fieldname !__fieldname_getter with
          | Some r ->
              r
          | None ->
              __fieldname_getter := Fieldname.Map.add fieldname false !__fieldname_getter ;
              false )
      | _ ->
          __fieldname_getter := Fieldname.Map.add fieldname false !__fieldname_getter ;
          false )


let resolve_methods proc classes =
  Typ.Name.Set.fold
    (fun this_class acc ->
      match resolve_method this_class proc with Some callee -> callee :: acc | None -> acc )
    classes []
