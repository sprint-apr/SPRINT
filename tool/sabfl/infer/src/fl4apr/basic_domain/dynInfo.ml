open! IStd
open! Vocab
module F = Format
module Node = InstrNode
module Context = BasicDom.Context
module Contexts = BasicDom.Contexts

module Key = struct
  type t = string * int * int [@@deriving compare]

  let pp fmt (filepath, line, label) = F.fprintf fmt "%s,%d,%d" filepath line label
end

module LabelMap = struct
  include PrettyPrintable.MakePPMonoMap (Key) (Node.Set)

  let add_elt k v t =
    match find_opt k t with
    | None ->
        add k (Node.Set.singleton v) t
    | Some nodes ->
        add k (Node.Set.add v nodes) t


  let rec find (classpath, line, label) t =
    match find_opt (classpath, line, label) t with
    | Some v ->
        v
    | None when Program.Class.is_testclass_str classpath ->
        raise (Unexpected "NoLabel")
    | None ->
        L.debug L.Analysis L.Quiet "[DynInfo]: No %a in the label_map@." Key.pp
          (classpath, line, label) ;
        raise (Unexpected "NoLabel")


  let find_call k t = Node.Set.filter Node.is_call_node (find k t)

  let find_load k t =
    Node.Set.filter (fun n -> match Node.get_instr n with Load _ -> true | _ -> false) (find k t)
end

let is_this_exp pdesc this_exp =
  match ASTExp.from_IR_exp_opt pdesc this_exp with
  | Some this_exp ->
      Procname.is_constructor (Procdesc.get_proc_name pdesc) && ASTExp.is_this this_exp
  | None ->
      false


module LineNodeMap = struct
  include PrettyPrintable.MakePPMap (Location)

  let add_elt (k : Location.t) v t =
    match find_opt k t with None -> add k [v] t | Some nodes -> add k (nodes @ [v]) t
end

let compute_label
    (cond_label_acc, invo_label_acc, switch_label_acc, cce_label_acc, oob_label_acc, catch_label_acc)
    pdesc =
  let nodes =
    Procdesc.get_nodes pdesc
    |> List.sort ~compare:(fun x y ->
           Procdesc.Node.compare_id (Procdesc.Node.get_id x) (Procdesc.Node.get_id y) )
  in
  let line_node_map =
    (* FIXME: lamba, anonymous class could have same line *)
    List.fold nodes ~init:LineNodeMap.empty ~f:(fun acc node ->
        let loc = Procdesc.Node.get_loc node in
        let instr_nodes = Node.list_of_pnode node in
        List.fold instr_nodes ~init:acc ~f:(fun acc instr_node ->
            LineNodeMap.add_elt loc instr_node acc ) )
  in
  let cls_str =
    match Procdesc.get_proc_name pdesc with
    | Procname.Java mthd ->
        Procname.Java.get_class_name mthd
    | _ as proc ->
        L.(die InternalError) "parse non-java methods: %a" Procname.pp proc
  in
  let cond_label =
    LineNodeMap.fold
      (fun _ instr_nodes acc ->
        let acc, _, _ =
          List.fold instr_nodes ~init:(acc, 0, 0) ~f:(fun (acc, tcnt, fcnt) instr_node ->
              match InstrNode.get_instr instr_node with
              | Sil.Prune (_, loc, true, _) ->
                  ( LabelMap.add_elt (cls_str, Location.(loc.line), tcnt) instr_node acc
                  , tcnt + 1
                  , fcnt )
              | Sil.Prune (_, loc, false, _) ->
                  ( LabelMap.add_elt (cls_str, Location.(loc.line), fcnt) instr_node acc
                  , tcnt
                  , fcnt + 1 )
              | _ ->
                  (acc, tcnt, fcnt) )
        in
        acc )
      line_node_map cond_label_acc
  in
  let switch_label =
    LineNodeMap.fold
      (fun _ instr_nodes acc ->
        List.fold instr_nodes ~init:acc ~f:(fun acc instr_node ->
            match InstrNode.get_instr instr_node with
            | Sil.Prune (_, loc, _, _) -> (
                let preds = Procdesc.Node.get_preds (Node.pnode_of instr_node) in
                match preds with
                | [pred] -> (
                  match Procdesc.Node.get_kind pred with
                  | Procdesc.Node.Stmt_node _ | Procdesc.Node.Join_node ->
                      LabelMap.add_elt (cls_str, Location.(loc.line), 0) instr_node acc
                  | _ ->
                      acc )
                | _ ->
                    acc )
            | _ ->
                acc ) )
      line_node_map switch_label_acc
  in
  let invo_label =
    LineNodeMap.fold
      (fun _ instr_nodes acc ->
        let acc, _ =
          List.fold instr_nodes ~init:(acc, 0) ~f:(fun (acc, cnt) instr_node ->
              match InstrNode.get_instr instr_node with
              | Sil.Call (_, Const (Cfun proc), _, _, _) when is_builtin_proc proc ->
                  (acc, cnt)
              | Sil.Call (_, Const (Cfun proc), (this_exp, _) :: _, _, _)
                when Procname.is_constructor proc && is_this_exp pdesc this_exp ->
                  (acc, cnt)
              | Sil.Call (_, _, _, _, {cf_virtual}) when cf_virtual ->
                  let loc = InstrNode.get_loc instr_node in
                  let pnode = InstrNode.pnode_of instr_node in
                  let acc =
                    Procdesc.Node.get_instrs pnode
                    |> Instrs.fold ~init:acc ~f:(fun acc instr ->
                           match instr with
                           | Sil.Load {id} when Ident.is_none id ->
                               let deref_node = InstrNode.of_pnode pnode instr in
                               LabelMap.add_elt (cls_str, Location.(loc.line), cnt) deref_node acc
                           | _ ->
                               acc )
                  in
                  (LabelMap.add_elt (cls_str, Location.(loc.line), cnt) instr_node acc, cnt + 1)
              | Sil.Call (_, _, _, _, _) ->
                  let loc = InstrNode.get_loc instr_node in
                  (LabelMap.add_elt (cls_str, Location.(loc.line), cnt) instr_node acc, cnt + 1)
              | _ ->
                  (acc, cnt) )
        in
        acc )
      line_node_map invo_label_acc
  in
  let cce_label, oob_label =
    LineNodeMap.fold
      (fun _ instr_nodes (cce_label_acc, oob_label_acc) ->
        List.fold instr_nodes ~init:(cce_label_acc, oob_label_acc)
          ~f:(fun (cce_label_acc, oob_label_acc) instr_node ->
            match InstrNode.get_instr instr_node with
            | Sil.Call (_, Const (Cfun proc), _, _, _) when Procname.equal proc BuiltinDecl.__cast
              ->
                let loc = InstrNode.get_loc instr_node in
                ( LabelMap.add_elt (cls_str, Location.(loc.line), 0) instr_node cce_label_acc
                , oob_label_acc )
            | Sil.Load {e= Lindex _} ->
                let loc = InstrNode.get_loc instr_node in
                ( cce_label_acc
                , LabelMap.add_elt (cls_str, Location.(loc.line), 0) instr_node oob_label_acc )
            | Sil.Store {e1= Lindex _} ->
                let loc = InstrNode.get_loc instr_node in
                ( cce_label_acc
                , LabelMap.add_elt (cls_str, Location.(loc.line), 0) instr_node oob_label_acc )
            | _ ->
                (cce_label_acc, oob_label_acc) ) )
      line_node_map (cce_label_acc, oob_label_acc)
  in
  let catch_label =
    LineNodeMap.fold
      (fun _ instr_nodes acc ->
        List.fold instr_nodes ~init:acc ~f:(fun acc instr_node ->
            match (InstrNode.get_instr instr_node, InstrNode.get_kind instr_node) with
            | ( Sil.Call (_, Const (Cfun proc), _, _, _)
              , Prune_node (_, _, PruneNodeKind_ExceptionHandler) )
              when Procname.equal proc BuiltinDecl.__instanceof ->
                (* TODO: add label only for catch statements *)
                let loc = InstrNode.get_loc instr_node in
                LabelMap.add_elt (cls_str, Location.(loc.line), 0) instr_node acc
            | _ ->
                acc ) )
      line_node_map catch_label_acc
  in
  (cond_label, invo_label, switch_label, cce_label, oob_label, catch_label)


module Value = struct
  type t = {br_info: AbsBool.t; class_info: Typ.Name.Set.t; die_info: AbsBool.t}
  [@@deriving compare]

  let pp fmt {br_info; class_info; die_info} =
    F.fprintf fmt "%a,%a,%a" AbsBool.pp br_info AbsBool.pp die_info Typ.Name.Set.pp class_info


  let join lhs rhs =
    { br_info= AbsBool.join lhs.br_info rhs.br_info
    ; class_info= Typ.Name.Set.union lhs.class_info rhs.class_info
    ; die_info= AbsBool.join lhs.die_info rhs.die_info }


  let bottom = {br_info= AbsBool.bottom; class_info= Typ.Name.Set.empty; die_info= AbsBool.bottom}

  let top = {br_info= AbsBool.top; class_info= Typ.Name.Set.empty; die_info= AbsBool.top}

  let get_br_info {br_info} = br_info

  let get_class_info {class_info} = class_info

  let get_die_info {die_info} = die_info
end

let is_target_ctx program : Context.t -> bool = function
  | Empty _ | Dummy ->
      true
  | Test (_, node) ->
      (* drop dyninfo for positive testcases *)
      Program.is_entry program (Node.get_proc_name node)


let parse_ctx ~testClass invo_label ctx_str =
  match String.split ctx_str ~on:',' with
  | [_] ->
      (* context of test setUp *)
      Contexts.singleton (Context.empty ~testClass)
  | [cls_str; line_str; label_str] ->
      let line = Int.of_string line_str in
      let label = Int.of_string label_str in
      let nodes =
        LabelMap.find (cls_str, line, label) invo_label |> Node.Set.filter Node.is_call_node
      in
      Node.Set.fold
        (fun n ->
          let ctx = Context.of_callsite ~testClass n in
          if is_target_ctx (Program.from_marshal ()) ctx then Contexts.add ctx
          else
            (* could be context of class initializer executed by other tests  *)
            Contexts.add (Context.empty ~testClass) )
        nodes Contexts.empty
  | _ as str_list ->
      raise
        (Unexpected (F.asprintf "invalid ctx str %s: %s" ctx_str (String.concat ~sep:"," str_list)))


let parse_cond_node cond_label key_str =
  match String.split key_str ~on:',' with
  | [cls_str; line_str; label_str] ->
      let line = Int.of_string line_str in
      let label = Int.of_string label_str in
      LabelMap.find (cls_str, line, label) cond_label
  | _ ->
      raise (Unexpected ("invalid cond str " ^ key_str))


let parse_invo_node invo_label key_str =
  match String.split key_str ~on:',' with
  | [cls_str; line_str; label_str] ->
      let line = Int.of_string line_str in
      let label = Int.of_string label_str in
      LabelMap.find (cls_str, line, label) invo_label
  | _ ->
      raise (Unexpected ("invalid invo str " ^ key_str))


let parse_exn_node exn_label key_str =
  match String.split key_str ~on:',' with
  | [cls_str; line_str] ->
      let line = Int.of_string line_str in
      LabelMap.find (cls_str, line, 0) exn_label
  | _ ->
      raise (Unexpected ("invalid invo str " ^ key_str))


let parse_cond_value value_str : AbsBool.t =
  match value_str with
  | "I" | "T" | "T,I" ->
      AbsBool.v true
  | "F" ->
      AbsBool.v false
  | "F,I" | "T,F" ->
      AbsBool.top
  | _ ->
      raise (Unexpected ("invalid invo str " ^ value_str))


let parse_class_value class_strs =
  List.map (String.split class_strs ~on:',') ~f:(fun class_str ->
      match String.split class_str ~on:'@' with
      | [class_str] ->
          java_class_from_string class_str
      | [_; class_str] ->
          (* to resolve concrete type of class.newInstance() *)
          Fl4aprModels.Class.from_underlying_string class_str
      | _ ->
          L.(die ExternalError) "Invalid classname format" )
  |> Typ.Name.Set.of_list


let parse_die_value die_str : AbsBool.t =
  match String.split die_str ~on:',' with
  | [int_str; bool_str] | [int_str; bool_str; _] ->
      let int_val = Int.of_string int_str in
      let has_passed = Bool.of_string bool_str in
      if Int.equal int_val 0 then AbsBool.v false
      else if has_passed then AbsBool.top
      else AbsBool.v true
  | _ ->
      L.(die ExternalError) "invalid die str %s" die_str


let parse_npe_value die_str : AbsBool.t =
  match String.split die_str ~on:',' with
  | [int_str; bool_str; npe_str] ->
      let int_val = Int.of_string int_str in
      let has_passed = Bool.of_string bool_str in
      let has_nped = Bool.of_string npe_str in
      if Int.equal int_val 0 then AbsBool.v false
      else if not has_nped then AbsBool.v false
      else if has_passed then AbsBool.top
      else AbsBool.v true
  | _ ->
      L.(die ExternalError) "invalid die str %s" die_str


let parse_catch_node catch_label key_str =
  match String.split key_str ~on:',' with
  | [cls_str; line_str] ->
      let line = Int.of_string line_str in
      LabelMap.find (cls_str, line, 0) catch_label
  | _ ->
      raise (Unexpected ("invalid catch str " ^ key_str))


let parse_switch_node switch_label (key_str, value_str) : (Node.Set.t * AbsBool.t) list =
  let switch_values =
    String.split value_str ~on:',' |> List.map ~f:Int.of_string |> Int.Set.of_list
  in
  match String.split key_str ~on:',' with
  | [cls_str; line_str; _] ->
      let line = Int.of_string line_str in
      let swtich_top_nodes = LabelMap.find (cls_str, line, 0) switch_label in
      let rec __parse switch_values node acc =
        let nodeset = Node.Set.singleton node in
        match Node.get_instr node with
        | Sil.Prune (BinOp (Binop.Eq, _, Const (Cint intlit)), _, _, _)
        | Sil.Prune (UnOp (Unop.LNot, BinOp (Binop.Eq, _, Const (Cint intlit)), _), _, _, _) ->
            let switch_value = IntLit.to_int_exn intlit in
            let true_value =
              if Int.Set.exists switch_values ~f:(Int.equal switch_value) then AbsBool.V true
              else AbsBool.bottom
            in
            let false_value =
              if Int.Set.exists switch_values ~f:(not <<< Int.equal switch_value) then
                AbsBool.V false
              else AbsBool.bottom
            in
            let node_key_value = (nodeset, AbsBool.join true_value false_value) in
            let switch_values = Int.Set.remove switch_values switch_value in
            let succs = Procdesc.Node.get_succs (InstrNode.pnode_of node) in
            List.fold succs ~init:(node_key_value :: acc) ~f:(fun acc pnode ->
                match get_instrs_list pnode with
                | _ :: (Sil.Prune (_, _, _, _) as instr) :: _
                | _ :: _ :: _ :: _ :: (Sil.Prune (_, _, _, _) as instr) :: _ ->
                    __parse switch_values (Node.of_pnode pnode instr) acc
                | _ ->
                    acc )
        | _ ->
            acc
      in
      Node.Set.fold (__parse switch_values) swtich_top_nodes []
  | _ ->
      raise (Unexpected ("invalid cond str " ^ key_str))


let find_proc_by_str class_str method_str args_str =
  let name = Typ.Name.Java.from_string class_str in
  let number_of_args =
    if String.is_empty args_str then 0 else List.length (String.split args_str ~on:',')
  in
  let methods_in_class = Program.methods_in_class (Program.from_marshal ()) name in
  let results =
    Procname.Set.filter
      (function
        | Procname.Java mthd ->
            String.equal method_str (Procname.Java.get_method mthd)
            && Int.equal number_of_args (Procname.Java.get_parameters mthd |> List.length)
        | _ ->
            false )
      methods_in_class
  in
  if (not (Procname.Set.is_empty methods_in_class)) && Procname.Set.is_empty results then
    L.debug L.Analysis L.Quiet
      "Could not find method for %s.%s(%s)@. - methods in class %a:@. [%a]@." class_str method_str
      args_str Typ.Name.pp name Procname.Set.pp methods_in_class ;
  results


let parse_method method_str : Procname.Set.t =
  match String.split_on_chars method_str ~on:['('; ')'] with
  | [method_name_str; args_str; ""] -> (
    match String.rsplit2 method_name_str ~on:'.' with
    | Some (class_str, method_str) ->
        (* try find proc by class_str.method_str *)
        let results = find_proc_by_str class_str method_str args_str in
        if Procname.Set.is_empty results then
          (* try find proc by class_str.method_str.<init> *)
          let class_str = String.concat ~sep:"." [class_str; method_str] in
          find_proc_by_str class_str "<init>" args_str
        else results
    | None ->
        raise (Unexpected (F.asprintf "invalid method str %s" method_str)) )
  | _ ->
      raise (Unexpected (F.asprintf "invalid method str %s" method_str))


module CtxMap = struct
  include PrettyPrintable.MakePPMonoMap (Context) (Value)

  let add ctx values t =
    match find_opt ctx t with
    | Some values' ->
        add ctx (Value.join values values') t
    | None ->
        add ctx values t
end

module NodeMap = PrettyPrintable.MakePPMonoMap (Node) (CtxMap)

type t = NodeMap.t

let pp = NodeMap.pp

let is_ctx_of_init ctx =
  match ctx with [callsite] -> Procname.is_constructor (Node.get_proc_name callsite) | _ -> false


let update ctx_nodes key_nodes values t =
  let program = Program.from_marshal () in
  let _update ctx acc_ctx =
    if is_target_ctx program ctx then CtxMap.add ctx values acc_ctx
      (* else if is_ctx_of_init ctx then CtxMap.add Context.empty values acc_ctx *)
    else acc_ctx
  in
  Node.Set.fold
    (fun node acc ->
      (* DEBUG *)
      match NodeMap.find_opt node acc with
      | Some ctx_map ->
          let ctx_map' = Contexts.fold _update ctx_nodes ctx_map in
          NodeMap.add node ctx_map' acc
      | None ->
          let ctx_map = Contexts.fold _update ctx_nodes CtxMap.empty in
          NodeMap.add node ctx_map acc )
    key_nodes t


let cache = ref NodeMap.empty

let marshalled_path = "dyninfo.data"

let to_marshal dyninfo =
  cache := dyninfo ;
  Utils.with_file_out marshalled_path ~f:(fun oc -> Marshal.to_channel oc dyninfo [])


let from_marshal () =
  if not is_sprint then NodeMap.empty
  else if NodeMap.is_empty !cache then (
    let dyninfo = Utils.with_file_in marshalled_path ~f:Marshal.from_channel in
    cache := dyninfo ;
    dyninfo )
  else !cache


let get_dynamic_exprs dyninfo ctxs node : Value.t =
  match Contexts.find_first_opt (not <<< Context.is_dummy) ctxs with
  | Some ctx -> (
    match NodeMap.find_opt node dyninfo with
    | Some ctx_map -> (
      match CtxMap.find_opt ctx ctx_map with Some values -> values | None -> Value.bottom )
    | None ->
        (* 3 possible cases:
           1. no dynamic state here (pruning chance)
           2. failed to parse
           3. failed to trace *)
        Value.bottom )
  | None ->
      Value.bottom


let get_dynamic_exprs dyninfo ctxs node : Value.t =
  if Config.sprint_no_test then Value.top else get_dynamic_exprs dyninfo ctxs node


let get_br_info ?(dyninfo = from_marshal ()) ctxs node =
  let br_info = get_dynamic_exprs dyninfo ctxs node |> Value.get_br_info in
  match Node.get_instr node with
  | Sil.Prune (UnOp (Unop.LNot, _, _), _, _, _) ->
      AbsBool.negate br_info
  | Sil.Prune (_, _, _, _) ->
      br_info
  | _ ->
      br_info


let get_class_info ?(dyninfo = from_marshal ()) ctxs node =
  get_dynamic_exprs dyninfo ctxs node |> Value.get_class_info


let get_die_info ?(dyninfo = from_marshal ()) ctxs node =
  get_dynamic_exprs dyninfo ctxs node |> Value.get_die_info |> AbsBool.negate


let _ctxs_per_proc : Contexts.t Procname.Map.t ref = ref Procname.Map.empty

let parse_exn dyninfo_exns ~invo_label exn_label ~testClass acc =
  List.fold dyninfo_exns ~init:acc ~f:(fun acc dyninfo_cce_str ->
      match String.split dyninfo_cce_str ~on:'/' with
      | [ctx_str; key_str; cce_str] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let cce_nodes = parse_exn_node exn_label key_str in
          let cce_value = parse_die_value cce_str in
          update ctx_nodes cce_nodes {Value.bottom with die_info= cce_value} acc
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "dyninfo invokedWell %s is not splitted " dyninfo_cce_str ;
          acc )


let parse_branch_info ~testClass ~invo_label cond_label dyninfo_brs init =
  List.fold dyninfo_brs ~init ~f:(fun acc dyninfo_str ->
      match String.split dyninfo_str ~on:'/' with
      | [ctx_str; key_str; value_str] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let key_nodes = parse_cond_node cond_label key_str in
          let values = parse_cond_value value_str in
          update ctx_nodes key_nodes {Value.bottom with br_info= values} acc
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "[Warning]: dyninfo branchTaken %s is not splitted@." dyninfo_str ;
          acc )


let parse_switch_info ~testClass ~invo_label switch_label dyninfo_switchs init =
  List.fold dyninfo_switchs ~init ~f:(fun acc dyninfo_str ->
      match String.split dyninfo_str ~on:'/' with
      | [ctx_str; key_str; value_str] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let key_value_list = parse_switch_node switch_label (key_str, value_str) in
          List.fold key_value_list ~init:acc ~f:(fun acc (key_nodes, values) ->
              update ctx_nodes key_nodes {Value.bottom with br_info= values} acc )
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "[Warning]: dyninfo swtich %s is not splitted@." dyninfo_str ;
          acc )


let parse_procs_info ~testClass ~invo_label dyninfo_procs =
  let ctxs_per_proc =
    List.fold dyninfo_procs ~init:Procname.Map.empty ~f:(fun acc dyninfo_proc_str ->
        match String.split dyninfo_proc_str ~on:'/' with
        | [method_str; invo_strs] ->
            let procs = parse_method method_str in
            let ctxs =
              List.filter_map (String.split invo_strs ~on:'@') ~f:(fun invo_str ->
                  try Some (parse_ctx ~testClass invo_label invo_str) with
                  | Unexpected "NoLabel" ->
                      None
                  | Unexpected msg ->
                      L.progress "[Warning]: %s@." msg ;
                      None )
              |> List.fold ~init:Contexts.empty ~f:(fun acc ctxs ->
                     Contexts.fold Contexts.add ctxs acc )
            in
            Procname.Set.fold
              (fun proc acc ->
                match Procname.Map.find_opt proc acc with
                | Some ctxs' ->
                    Procname.Map.add proc (Contexts.union ctxs ctxs') acc
                | None ->
                    Procname.Map.add proc ctxs acc )
              procs acc
        | _ ->
            L.progress "dyninfo invokedMethods %s is not splitted@." dyninfo_proc_str ;
            acc )
  in
  _ctxs_per_proc :=
    Procname.Map.merge
      (fun _ o1 o2 ->
        match (o1, o2) with
        | Some c1, Some c2 ->
            Some (Contexts.union c1 c2)
        | Some c, None | None, Some c ->
            Some c
        | None, None ->
            None )
      !_ctxs_per_proc ctxs_per_proc


let parse_invoClass_info ~testClass ~invo_label dyninfo_invos init =
  List.fold dyninfo_invos ~init ~f:(fun acc dyninfo_str ->
      match String.split dyninfo_str ~on:'/' with
      | [ctx_str; key_str; class_str] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let key_nodes = Node.Set.filter Node.is_call_node (parse_invo_node invo_label key_str) in
          let values = parse_class_value class_str in
          update ctx_nodes key_nodes {Value.bottom with class_info= values} acc
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "[Warning]: dyninfo invokedClass %s is not splitted@." dyninfo_str ;
          acc )


let parse_invokedWell_info ~testClass ~invo_label dyninfo_dies init =
  List.fold dyninfo_dies ~init ~f:(fun acc dyninfo_die_str ->
      match String.split dyninfo_die_str ~on:'/' with
      | [ctx_str; key_str; die_str] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let call_nodes, deref_nodes =
            Node.Set.partition Node.is_call_node (parse_invo_node invo_label key_str)
          in
          let die_values = parse_die_value die_str in
          let npe_values = parse_npe_value die_str in
          update ctx_nodes call_nodes {Value.bottom with die_info= die_values} acc
          |> update ctx_nodes deref_nodes {Value.bottom with die_info= npe_values}
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "dyninfo invokedWell %s is not splitted " dyninfo_die_str ;
          acc )


let parse_catch_info ~testClass ~invo_label catch_label dyninfo_catchs init =
  List.fold dyninfo_catchs ~init ~f:(fun acc dyninfo_str ->
      match String.split dyninfo_str ~on:'/' with
      | [ctx_str; key_str; _] -> (
        try
          let ctx_nodes = parse_ctx ~testClass invo_label ctx_str in
          let key_nodes = parse_catch_node catch_label key_str in
          let values = (* sound decision *) AbsBool.top in
          update ctx_nodes key_nodes {Value.bottom with br_info= values} acc
        with
        | Unexpected "NoLabel" ->
            acc
        | Unexpected msg ->
            L.progress "[Warning]: %s@." msg ;
            acc )
      | _ ->
          L.progress "[Warning]: dyninfo catch %s is not splitted@." dyninfo_str ;
          acc )


let parse_dyninfo_class ~testClass ~cond_label ~invo_label ~switch_label ~cce_label ~oob_label
    ~catch_label init =
  let className = Typ.Name.name testClass in
  let path_br = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_br in
  let path_switch = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_switch in
  let path_invo = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_invo in
  let path_die = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_die in
  let path_proc = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_proc in
  let path_cce = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_cce in
  let path_oob = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_oob in
  let path_catch = Config.sprint_dyninfo_dir ^/ className ^/ Config.sprint_dyninfo_catch in
  match
    ( Utils.read_file path_br
    , Utils.read_file path_switch
    , Utils.read_file path_invo
    , Utils.read_file path_die
    , Utils.read_file path_proc
    , Utils.read_file path_cce
    , Utils.read_file path_oob
    , Utils.read_file path_catch )
  with
  | ( Ok dyninfo_brs
    , Ok dyninfo_switchs
    , Ok dyninfo_invos
    , Ok dyninfo_dies
    , Ok dyninfo_procs
    , Ok dyninfo_cces
    , Ok dyninfo_oobs
    , Ok dyninfo_catchs ) ->
      parse_procs_info ~testClass ~invo_label dyninfo_procs ;
      parse_branch_info ~testClass ~invo_label cond_label dyninfo_brs init
      |> parse_switch_info ~testClass ~invo_label switch_label dyninfo_switchs
      |> parse_invoClass_info ~testClass ~invo_label dyninfo_invos
      |> parse_exn dyninfo_cces ~testClass ~invo_label cce_label
      |> parse_exn dyninfo_oobs ~testClass ~invo_label oob_label
      |> parse_invokedWell_info ~testClass ~invo_label dyninfo_dies
      |> parse_catch_info ~testClass ~invo_label catch_label dyninfo_catchs
  | _ ->
      L.(die ExternalError) "No %s or %s or %s or %s" path_br path_invo path_die path_proc


let test_classes_executed program =
  let all_test_classes = Program.all_classes program |> List.filter ~f:Program.Class.is_testclass in
  List.filter all_test_classes ~f:(fun name ->
      match Sys.is_directory (Config.sprint_dyninfo_dir ^/ Typ.Name.name name) with
      | `Yes ->
          true
      | _ ->
          false )


let parse_dyninfo program =
  let all_pdescs =
    Procname.Set.fold
      (fun proc acc ->
        match Program.pdesc_of_opt program proc with Some pdesc -> pdesc :: acc | _ -> acc )
      (Program.all_procs program) []
  in
  let test_classes_executed = test_classes_executed program in
  L.progress "Test classes executed: %a@." (Pp.seq ~sep:"\n" Typ.Name.pp) test_classes_executed ;
  let cond_label, invo_label, switch_label, cce_label, oob_label, catch_label =
    List.fold all_pdescs
      ~init:
        ( LabelMap.empty
        , LabelMap.empty
        , LabelMap.empty
        , LabelMap.empty
        , LabelMap.empty
        , LabelMap.empty )
      ~f:compute_label
  in
  print_to_file
    ~msg:
      (F.asprintf "cond label: %a@.@. invo_label: %a@.@.switch_label: %a@.@." LabelMap.pp cond_label
         LabelMap.pp invo_label LabelMap.pp switch_label )
    ~filename:"cond_invo_label_map.results" ~dirname:None ;
  print_to_file
    ~msg:(F.asprintf "%a" LabelMap.pp switch_label)
    ~filename:"switch_label_map.results" ~dirname:None ;
  let results =
    List.fold test_classes_executed ~init:NodeMap.empty ~f:(fun acc testClass ->
        parse_dyninfo_class ~testClass ~cond_label ~invo_label ~switch_label ~cce_label ~oob_label
          ~catch_label acc )
  in
  print_to_file
    ~msg:(F.asprintf "ctxs_per_proc: %a@." (Procname.Map.pp ~pp_value:Contexts.pp) !_ctxs_per_proc)
    ~filename:"ctxs_per_proc.results" ~dirname:None ;
  to_marshal results ;
  results


let _all_ctxs = ref None

let all_ctxs () : Contexts.t =
  let program = Program.from_marshal () in
  match !_all_ctxs with
  | Some all_ctxs ->
      all_ctxs
  | None ->
      let all_ctxs =
        NodeMap.fold
          (fun _ ctx_map acc ->
            CtxMap.fold
              (fun ctx _ acc ->
                if Context.is_empty ctx || is_target_ctx program ctx then Contexts.add ctx acc
                else acc )
              ctx_map acc )
          !cache
          (Contexts.singleton Context.dummy)
      in
      _all_ctxs := Some all_ctxs ;
      let msg =
        Contexts.fold
          (fun ctx acc_msg ->
            match ctx with
            | Test _ ->
                F.asprintf "Context: %a@.%s" Context.pp ctx acc_msg
            | _ ->
                acc_msg )
          all_ctxs ""
      in
      print_to_file ~dirname:None ~msg ~filename:"contexts" ;
      all_ctxs


let _all_test_nodes = ref None

let all_test_nodes () : Node.Set.t =
  match !_all_test_nodes with
  | Some all_test_nodes ->
      all_test_nodes
  | None ->
      let all_ctxs = all_ctxs () in
      let all_test_nodes =
        Contexts.fold
          (function Test (_, node) -> Node.Set.add node | _ -> fun x -> x)
          all_ctxs Node.Set.empty
      in
      _all_test_nodes := Some all_test_nodes ;
      all_test_nodes


let _procs_to_ctxs : Contexts.t list Procname.Map.t ref = ref Procname.Map.empty

module ValuesCtxMap = WeakMap.Make (Value) (Contexts)

let visited_ctxs proc =
  match Procname.Map.find_opt proc !_ctxs_per_proc with
  | Some visited ->
      visited
  | None ->
      Contexts.empty


let ctxs_of_proc proc =
  match Procname.Map.find_opt proc !_procs_to_ctxs with
  | Some x ->
      x
  | None ->
      let program = Program.from_marshal () in
      let ctxs_unvisited = Contexts.singleton Context.dummy in
      Procname.Set.iter
        (fun proc ->
          let visited_ctxs = visited_ctxs proc in
          match proc with
          | Procname.Java mthd when Program.is_entry program proc ->
              (* Some entries could not visited if test failed during setup *)
              let testClass = Procname.Java.get_class_type_name mthd in
              let entry_context = Context.empty ~testClass in
              let contexts = Contexts.add entry_context visited_ctxs in
              let ctxs_list = List.map (Contexts.elements contexts) ~f:Contexts.singleton in
              _procs_to_ctxs := Procname.Map.add proc ctxs_list !_procs_to_ctxs
          | _ when Contexts.is_empty visited_ctxs ->
              _procs_to_ctxs := Procname.Map.add proc [ctxs_unvisited] !_procs_to_ctxs
          | _ ->
              let visited = Procname.Map.find proc !_ctxs_per_proc in
              _procs_to_ctxs := Procname.Map.add proc [ctxs_unvisited; visited] !_procs_to_ctxs )
        (Program.all_procs program) ;
      NodeMap.iter
        (fun n ctx_map ->
          let proc = Node.get_proc_name n in
          if not (Program.is_entry program proc) then
            let value_ctxs_map =
              CtxMap.fold
                (fun ctx values acc ->
                  if Context.is_empty ctx || is_target_ctx program ctx then
                    ValuesCtxMap.weak_update values (Contexts.singleton ctx) acc
                  else acc )
                ctx_map ValuesCtxMap.empty
            in
            let ctxs_with_values =
              ValuesCtxMap.fold (fun _ ctxs -> Contexts.union ctxs) value_ctxs_map Contexts.empty
            in
            let ctxs_visited = visited_ctxs proc in
            let ctxs_with_no_values = Contexts.diff ctxs_visited ctxs_with_values in
            let value_ctxs_map =
              ValuesCtxMap.weak_update Value.bottom ctxs_with_no_values value_ctxs_map
            in
            let ctxs_new =
              List.concat_map (Procname.Map.find proc !_procs_to_ctxs) ~f:(fun ctxs1 ->
                  ValuesCtxMap.fold
                    (fun _ ctxs2 acc ->
                      if Contexts.disjoint ctxs1 ctxs2 then acc
                      else Contexts.inter ctxs1 ctxs2 :: acc )
                    value_ctxs_map [] )
            in
            _procs_to_ctxs := Procname.Map.add proc (ctxs_unvisited :: ctxs_new) !_procs_to_ctxs )
        !cache ;
      ( if Config.debug_mode && Config.sprint_preanal then
        let msg =
          Procname.Map.fold
            (fun proc ctxs_list acc ->
              F.asprintf "%s@.@.-------------- contexts list for %a -------------------@. - %a" acc
                Procname.pp proc (Pp.seq ~sep:"\n - " Contexts.pp) ctxs_list )
            !_procs_to_ctxs ""
        in
        print_to_file ~msg ~dirname:None ~filename:"procs_to_ctxs" ) ;
      Procname.Map.find proc !_procs_to_ctxs


let ctxs_of_proc_visited proc =
  List.filter (ctxs_of_proc proc) ~f:(not <<< Contexts.exists Context.is_dummy)
  |> List.fold ~init:Contexts.empty ~f:Contexts.union
