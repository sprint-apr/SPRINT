open! IStd
open! Vocab
module Node = InstrNode
module L = Logging

let pgm = lazy (Program.from_marshal ())

module Hole = struct
  let atom = Exp.Const (Cstr "FL4APR_HOLE")

  let is_hole e = Exp.equal e atom

  let create typ = Exp.Cast (typ, atom)
end

type result = SAT | UnSAT | NoChange | ExnSAT | ExnUnSAT | Unexecuted | Unsound

type status = Feasible | NoExnSat | Unreachable | ExistExnSat | Infeasible

type description =
  | WrongExp of (Exp.t * Typ.t)
  | MissingSideEffect of Pvar.t * Fieldname.t
  | MissingErrorHandling of [`Return | `Throw of Typ.t]
  | ShouldSkip
[@@deriving compare]

type node = Node.t [@@deriving compare]

type location = Inplace of node | Before of node | After of node | Range of location * location
[@@deriving compare]

type t =
  { id: int
  ; desc: description
  ; loc: location
  ; org_instr: Sil.instr
  ; new_instrs: Sil.instr list
  ; score: float
  ; mutable results: result Array.t
  ; mutable status: status
  ; mutable is_redundant: bool }

let compare x y = x.id - y.id

let equal x y = Int.equal x.id y.id

let __count = ref 0

let new_id () =
  __count := !__count + 1 ;
  !__count


let create ~score desc loc org_instr new_instrs =
  { id= new_id ()
  ; score
  ; desc
  ; loc
  ; org_instr
  ; new_instrs
  ; results= Array.create ~len:(List.length Config.sprint_test_methods) Unexecuted
  ; status= Unreachable
  ; is_redundant= false }


let mk_missing_error_handling ~score ~hkind ~loc =
  create ~score (MissingErrorHandling hkind) loc Sil.skip_instr []


let rec get_location_node = function
  | Inplace n | Before n | After n ->
      n
  | Range (l, _) ->
      get_location_node l


let get_proc_name {loc} = get_location_node loc |> InstrNode.get_proc_name

let get_line_file {loc} =
  let Location.{line; file} = get_location_node loc |> InstrNode.get_loc in
  (line, SourceFile.to_string file)


let pp fmt {desc; loc; new_instrs; id} =
  let at_str =
    match loc with
    | Inplace node | Before node | After node ->
        F.asprintf "%s:%a"
          (node |> Node.get_proc_name |> Procname.get_method)
          Procdesc.Node.pp_id
          (node |> Node.pnode_of |> Procdesc.Node.get_id)
    | Range (Before n_from, Before n_to) | Range (Before n_from, After n_to) ->
        F.asprintf "%s:%a_%a"
          (n_from |> Node.get_proc_name |> Procname.get_method)
          Procdesc.Node.pp_id
          (n_from |> Node.pnode_of |> Procdesc.Node.get_id)
          Procdesc.Node.pp_id
          (n_to |> Node.pnode_of |> Procdesc.Node.get_id)
    | _ ->
        L.(die InternalError) "Invalid fault"
  in
  ( match desc with
  | WrongExp _ ->
      F.fprintf fmt "Replace[%a]" (Sil.pp_instr ~print_types:false Pp.text) (List.hd_exn new_instrs)
  | MissingSideEffect (pv, f) ->
      F.fprintf fmt "Modify[%a.%s]_%s" Pvar.pp_value pv (Fieldname.to_simplified_string f) at_str
  | MissingErrorHandling `Return ->
      F.fprintf fmt "Return_%s" at_str
  | MissingErrorHandling (`Throw exn_typ) ->
      F.fprintf fmt "Throw_%a_%s" (Typ.pp_full Pp.text) exn_typ at_str
  | ShouldSkip ->
      F.fprintf fmt "Skip_%s" at_str ) ;
  F.fprintf fmt "(%d)" id


let rec pp_full fmt {id; desc; loc; org_instr; new_instrs} =
  let old_instrs =
    loc |> get_location_node |> Node.pnode_of |> Procdesc.Node.get_instrs
    |> Instrs.get_underlying_not_reversed |> Array.to_list
  in
  F.fprintf fmt "{@[<v2>@,%12s: %d@, %12s: %a@,%12s: %a@,%12s: %a@,%12s: %a@,%12s: %a@]@,}" "ID" id
    "Description" pp_desc desc "Location" pp_loc loc "Org. Instr"
    (Sil.pp_instr ~print_types:true Pp.text)
    org_instr "New Instrs" pp_instrs new_instrs "Old Instrs" pp_instrs old_instrs


and pp_desc fmt = function
  | WrongExp (e, ty) ->
      F.fprintf fmt "WrongExp_(%a,%a)" Exp.pp e (Typ.pp_full Pp.text) ty
  | MissingSideEffect (pv, fn) ->
      F.fprintf fmt "MissingSideEffect_(%a,%a)" (Pvar.pp Pp.text) pv Fieldname.pp fn
  | MissingErrorHandling hkind ->
      F.fprintf fmt "MissingErrorHandling_(%s)"
        ( match hkind with
        | `Return ->
            "Return"
        | `Throw exn_typ ->
            F.asprintf "Throw (%a)" (Typ.pp_full Pp.text) exn_typ )
  | ShouldSkip ->
      F.fprintf fmt "ShouldSkip"


and pp_loc fmt = function
  | Inplace n ->
      F.fprintf fmt "Inplace %a" pp_node n
  | Before n ->
      F.fprintf fmt "Before %a" pp_node n
  | After n ->
      F.fprintf fmt "After %a" pp_node n
  | Range (s, d) ->
      F.fprintf fmt "Range @[<v>from:%a@,to:%a@]" pp_loc s pp_loc d


and pp_node fmt Node.{inode} =
  let Location.{file; line} = InterNode.get_loc inode in
  F.fprintf fmt "(%s_%a, Line %d on %a)"
    (Procname.get_method (InterNode.get_proc_name inode))
    Procdesc.Node.pp (InterNode.pnode_of inode) line SourceFile.pp file


and pp_instrs fmt instrs =
  match instrs with
  | [] ->
      F.fprintf fmt "[]"
  | [instr] ->
      F.fprintf fmt "[%a]" (Sil.pp_instr ~print_types:true Pp.text) instr
  | _ ->
      F.fprintf fmt "[@[<v2>%a@]@,]"
        (fun fmt instrs ->
          List.iter instrs ~f:(fun instr ->
              F.fprintf fmt "@,%a" (Sil.pp_instr ~print_types:true Pp.text) instr ) )
        instrs


let to_string_result = function
  | Unexecuted ->
      "Unexecuted"
  | SAT ->
      "Sat"
  | UnSAT ->
      "Unsat"
  | NoChange ->
      "No change"
  | ExnSAT ->
      "ExnSat"
  | ExnUnSAT ->
      "ExnUnSat"
  | Unsound ->
      "Unsound"


let to_string_status = function
  | Feasible ->
      "Feasible"
  | NoExnSat ->
      "NoExnSat"
  | Unreachable ->
      "Unreachable"
  | ExistExnSat ->
      "ExistExnSat"
  | Infeasible ->
      "Infeasible"


let pp_results fmt {status; results} =
  F.fprintf fmt "%s,%a" (to_string_status status)
    (Pp.seq ~sep:"," (Pp.of_string ~f:to_string_result))
    (Array.to_list results)


let marshal_path = Filename.concat Config.results_dir "abs_patches.data"

let _all_abs_patches = ref String.Map.empty

let to_marshal ?(path = marshal_path) abs_patches =
  Utils.with_file_out path ~f:(fun oc -> Marshal.to_channel oc abs_patches [])


let from_marshal ?(path = marshal_path) () =
  match String.Map.find !_all_abs_patches path with
  | None ->
      let abs_patches =
        match Sys.file_exists path with
        | `Yes ->
            Utils.with_file_in path ~f:Marshal.from_channel
        | _ ->
            []
      in
      _all_abs_patches := String.Map.add_exn ~key:path ~data:abs_patches !_all_abs_patches ;
      abs_patches
  | Some abs_patches ->
      abs_patches


let _all_fault_procs = ref None

let all_fault_procs () =
  match !_all_fault_procs with
  | Some procs ->
      procs
  | None ->
      let all_abs_patches = from_marshal () in
      let all_fault_procs =
        List.fold all_abs_patches ~init:Procname.Set.empty ~f:(fun acc fault ->
            Procname.Set.add (get_proc_name fault) acc )
      in
      _all_fault_procs := Some all_fault_procs ;
      all_fault_procs


let first_instr_node node = node |> InterNode.pnode_of |> InstrNode.list_of_pnode |> List.hd_exn

let find_most ~is_first nodes =
  let node_set = InterNode.Set.of_list nodes in
  let get_nears = if is_first then InterNode.get_preds else InterNode.get_succs in
  List.find_exn nodes ~f:(fun n ->
      List.for_all (get_nears n) ~f:(fun pred -> not (InterNode.Set.mem pred node_set)) )


let first_inter_node_at_location location =
  Program.find_node_with_location !!pgm location
  |> List.filter ~f:(not <<< Procdesc.Node.(equal_nodekind Start_node) <<< InterNode.get_kind)
  |> List.filter ~f:(not <<< List.is_empty <<< InterNode.get_preds)
  |> find_most ~is_first:true


let last_inter_node_at_location location =
  Program.find_node_with_location !!pgm location
  |> List.filter ~f:(not <<< Procdesc.Node.(equal_nodekind Start_node) <<< InterNode.get_kind)
  |> List.filter ~f:(not <<< List.is_empty <<< InterNode.get_preds)
  |> find_most ~is_first:false


let find_non_synthetic_switch_nodes location =
  Program.find_node_with_location !!pgm location
  |> List.concat_map ~f:(fun (_, inode) -> InstrNode.list_of_pnode inode)
  |> List.filter ~f:(fun InstrNode.{instr} ->
         match instr with
         | Sil.Prune (_, _, _, ik) when not (Sil.equal_if_kind ik Sil.Ik_switch) ->
             true
         | _ ->
             false )


module WrongExp = struct
  let type_of_const : Const.t -> Typ.t = function
    | Cint intlit when IntLit.isnull intlit ->
        Typ.pointer_to_java_lang_object
    | Cint _ ->
        Typ.int
    | Cfloat _ ->
        Typ.float
    | Cstr _ ->
        Typ.pointer_to_java_lang_string
    | Cclass _ ->
        Typ.pointer_to_java_lang_object
    | Cfun _ as c ->
        L.die InternalError "function names cannot appear in prune: %a" (Const.pp Pp.text) c


  let rec enumerate location =
    let tenv = Ident.Hash.create 8 in
    let nodes =
      if Program.CFG.is_switch_location location then find_non_synthetic_switch_nodes location
      else
        Program.find_node_with_location !!pgm location
        |> List.concat_map ~f:(InterNode.pnode_of >>> InstrNode.list_of_pnode)
    in
    List.concat_map nodes ~f:(enum_on_instr_node ~tenv)


  and enum_on_instr_node (Node.{instr} as node) ~tenv =
    let pdesc = Program.pdesc_of (Program.from_marshal ()) (Node.get_proc_name node) in
    ( match instr with
    | Sil.Load {id; typ} | Call ((id, typ), _, _, _, _) ->
        Ident.Hash.add tenv id typ
    | _ ->
        () ) ;
    let create org_exp org_typ new_instr =
      (* Explicit type representation for boolean-integers *)
      let ty' =
        match instr with
        | (Sil.Load {e= Lvar pv} | Sil.Store {e1= Lvar pv})
          when Option.value_map (Program.get_pvar_typ_opt pv) ~default:false
                 ~f:(Typ.equal Typ.boolean) ->
            Typ.boolean
        | _ ->
            org_typ
      in
      create (WrongExp (org_exp, ty')) (Inplace node) instr [new_instr]
    in
    let open Sil in
    match instr with
    | Load {id; e= Var id'; root_typ; typ; loc} when Ident.is_none id ->
        (* replace derefenced expression *)
        [create (Var id') typ (Load {id= id'; e= Hole.create typ; root_typ; loc; typ})]
    | Store {e2= Exn _} ->
        []
    | Store {e1= Lvar pv} when Pvar.is_frontend_tmp pv ->
        []
    | Store ({e2; typ} as store) ->
        let rec enumerate (e : Exp.t) subtyp : (Exp.t * Typ.t * Exp.t) list =
          match e with
          | Exp.Cast (t, e) -> (
            match ASTExp.typeof_exp_opt pdesc e with
            | Some subtyp ->
                let result = enumerate e subtyp in
                List.map result ~f:(fun (e_org, subtyp, e_rep) ->
                    if Exp.equal e e_org then (Exp.Cast (t, e_org), typ, Exp.Cast (t, e_rep))
                    else (e_org, subtyp, Exp.Cast (t, e_rep)) )
            | None ->
                [(e, subtyp, Hole.create subtyp)] )
          | Exp.BinOp (binop, e_lhs, e_rhs) ->
              let whole = (e, subtyp, Hole.create subtyp) in
              let lhs =
                Option.value_map (ASTExp.typeof_exp_opt pdesc e) ~default:[] ~f:(fun subtyp ->
                    List.map (enumerate e_lhs subtyp) ~f:(fun (e_org, subtyp_lhs, e_rep_lhs) ->
                        (e_org, subtyp_lhs, Exp.BinOp (binop, e_rep_lhs, e_rhs)) ) )
              in
              let rhs =
                Option.value_map (ASTExp.typeof_exp_opt pdesc e) ~default:[] ~f:(fun subtyp ->
                    List.map (enumerate e_rhs subtyp) ~f:(fun (e_org, subtyp_rhs, e_rep_rhs) ->
                        (e_org, subtyp_rhs, Exp.BinOp (binop, e_lhs, e_rep_rhs)) ) )
              in
              (whole :: lhs) @ rhs
          | e ->
              [(e, subtyp, Hole.create subtyp)]
        in
        List.map (enumerate e2 typ) ~f:(fun (e_org, subtyp, e_rep) ->
            create e_org subtyp (Store {store with e2= e_rep}) )
    | Prune (UnOp (Unop.LNot, BinOp _, _), _, _, _) ->
        []
    | Prune ((BinOp _ as pe), loc, b, ifkind) ->
        [create pe Typ.boolean (Prune (Hole.create Typ.boolean, loc, b, ifkind))]
    | Call
        ( (ret_id, ret_typ)
        , (Const (Cfun proc) as fe)
        , [(Exp.Sizeof ({dynamic_length= Some e_len} as sizeof_data), arg_typ)]
        , loc
        , cf )
      when is_new proc ->
        let new_instr =
          Call
            ( (ret_id, ret_typ)
            , fe
            , [(Exp.Sizeof {sizeof_data with dynamic_length= Some (Hole.create Typ.int)}, arg_typ)]
            , loc
            , cf )
        in
        let fault = create e_len Typ.int new_instr in
        [fault]
    | Call ((ret_id, ret_typ), Const (Cfun proc), _, loc, _)
      when Procname.equal BuiltinDecl.__cast proc ->
        (* replace (T) e*)
        let new_instr =
          Load {id= ret_id; e= Hole.create ret_typ; root_typ= ret_typ; typ= ret_typ; loc}
        in
        [create (Exp.Var ret_id) ret_typ new_instr]
    | Call ((ret_id, ret_typ), (Const (Cfun (Java mthd)) as fe), args, loc, cf) ->
        let all_replaced =
          let new_instr =
            Load {id= ret_id; e= Hole.create ret_typ; root_typ= ret_typ; typ= ret_typ; loc}
          in
          create (Exp.Var ret_id) ret_typ new_instr
        in
        let param_types = Procname.Java.get_parameters mthd in
        let is_static = Procname.Java.is_static mthd in
        all_replaced
        :: List.filter_mapi args ~f:(fun idx (argexp, argtyp) ->
               if is_static || not (Int.equal 0 idx) then
                 let resolved_argtyp =
                   let param_type = List.nth_exn param_types (idx - if is_static then 0 else 1) in
                   if Exp.is_const argexp && Typ.equal param_type Typ.boolean then Typ.boolean
                   else argtyp
                 in
                 let punched =
                   let arr = List.to_array args in
                   arr.(idx) <- (Hole.create resolved_argtyp, resolved_argtyp) ;
                   Array.to_list arr
                 in
                 Some
                   (create argexp resolved_argtyp (Call ((ret_id, ret_typ), fe, punched, loc, cf)))
               else (* redundant fault which replace dereferenced expression *)
                 None )
    | _ ->
        []


  and enum_holes_on_lvalue e typ =
    match (e : Exp.t) with
    | Var _ ->
        [] (* do not mutate ident *)
    | Cast _ ->
        L.(die InternalError) "%a is not allowed as rvalue in java" Exp.pp e
    | Lindex (base, idx) ->
        (* We do not go into the sub-expression of idx recursively*)
        let base_hole =
          let ty_base = Typ.mk_array typ in
          (Exp.Lindex (Hole.create ty_base, idx), base, ty_base)
        in
        let index_hole = (Exp.Lindex (base, Hole.create Typ.int), idx, Typ.int) in
        [base_hole; index_hole]
    | Lfield (base, fn, ty_base) -> (
        let entire_hole = (Hole.create typ, e, typ) in
        match base with
        | Lvar pv when Pvar.is_global pv ->
            (* Do not create base hole for static field access *)
            [entire_hole]
        | _ ->
            let base_hole = (Exp.Lfield (Hole.create ty_base, fn, ty_base), base, ty_base) in
            [entire_hole; base_hole] )
    | Lvar _ ->
        [(Hole.create typ, e, typ)]
    | _ ->
        []


  and enum_holes_on_rvalue ?(tenv = Ident.Hash.create 8) e =
    match (e : Exp.t) with
    | Const c ->
        let ty = type_of_const c in
        [(Hole.create ty, e, ty)]
    | UnOp (op, e, tyopt) ->
        let holes = enum_holes_on_rvalue e ~tenv in
        List.map holes ~f:(fun (hole, org, typ') -> (Exp.UnOp (op, hole, tyopt), org, typ'))
    | BinOp (bo, (Var id as le), re) ->
        let ty = Ident.Hash.find tenv id in
        [(Exp.BinOp (bo, Hole.create ty, re), le, ty); (Exp.BinOp (bo, le, Hole.create ty), re, ty)]
    | Cast (typ, e) ->
        let holes = enum_holes_on_rvalue e in
        List.map holes ~f:(fun (hole, org, typ') -> (Exp.Cast (typ, hole), org, typ'))
    | Exn _ ->
        []
    | Var _ | BinOp _ | Closure _ | Sizeof _ ->
        []
    | Lvar _ | Lfield _ | Lindex _ ->
        L.(die InternalError) "%a is not allowed as rvalue in java" (Exp.pp_texp_full Pp.text) e
end

module MissingErrorHandling = struct
  let __expected_exceptions = ref None

  let expected_exceptions failing_test_methods =
    match !__expected_exceptions with
    | Some expected_exceptions ->
        expected_exceptions
    | None ->
        let module TypSet = Caml.Set.Make (Typ) in
        let expected_exceptions =
          List.fold failing_test_methods ~init:[] ~f:(fun acc (_, mthd) ->
              ( Program.get_expected_exn_typ !!pgm mthd
              |> Option.value_map ~default:acc ~f:(fun exn -> exn :: acc) )
              @ ( Program.pdesc_of !!pgm mthd |> Procdesc.get_nodes
                |> List.fold ~init:[] ~f:(fun acc node ->
                       Instrs.fold (Procdesc.Node.get_instrs node) ~init:acc ~f:(fun acc -> function
                         | Sil.Call
                             ( _
                             , Const (Cfun proc)
                             , [_; (Exp.Sizeof {typ= Typ.{desc= Tstruct name} as typ}, _)]
                             , _
                             , _ )
                           when Procname.equal BuiltinDecl.__instanceof proc
                                && Fl4aprModels.implements_interfaces ["java.lang.Exception"] name
                           ->
                             typ :: acc
                         | _ ->
                             acc ) ) ) )
          |> TypSet.of_list |> TypSet.elements
        in
        __expected_exceptions := Some expected_exceptions ;
        expected_exceptions


  let enumerate location =
    let enum_on_fault_location loc =
      let exn_typs =
        let expected_typs = expected_exceptions (Program.get_failing_test_methods !!pgm) in
        if List.is_empty expected_typs then
          [Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Exception")]
        else expected_typs
      in
      List.concat
        [ [mk_missing_error_handling ~hkind:`Return ~loc]
        ; List.map exn_typs ~f:(fun exn_typ ->
              mk_missing_error_handling ~hkind:(`Throw exn_typ) ~loc ) ]
    in
    if Program.CFG.is_switch_location location then
      find_non_synthetic_switch_nodes location
      |> List.concat_map ~f:(fun node -> enum_on_fault_location (After node))
    else
      let internode = location |> first_inter_node_at_location in
      let has_bool_ret : Sil.instr -> bool = function
        | Sil.Store {e1= Lvar pv; typ} when Pvar.is_return pv && Typ.equal typ Typ.boolean ->
            true
        | _ ->
            false
      in
      if InterNode.get_instrs internode |> Instrs.exists ~f:has_bool_ret then []
      else enum_on_fault_location (Before (first_instr_node internode))
end

module MissingSideEffect = struct
  let get_parameters pgm procname =
    let pdesc = Program.pdesc_of pgm procname in
    let parameters = Procdesc.get_pvar_formals pdesc in
    let escaped_locals =
      List.filter_map (Program.get_nodes pgm procname) ~f:(fun (_, node) ->
          match get_instrs_list node with
          | Load {id; e= Lvar pv; typ} :: Store {e1= Lvar retvar; e2= Var id'} :: _
            when Ident.equal id id' && Pvar.is_return retvar && Pvar.is_local pv ->
              Some (pv, typ)
          | _ ->
              None )
    in
    escaped_locals @ parameters


  let loaded_parameters_on node =
    let parameters = get_parameters !!pgm (InterNode.get_proc_name node) in
    let instrs = Instrs.fold (InterNode.get_instrs node) ~f:(fun acc i -> i :: acc) ~init:[] in
    List.concat_map instrs ~f:(function
      | Sil.Load {e; typ= {desc= Tptr ({desc= Tstruct klass}, _)}} ->
          IRUtils.fold_expr ~init:[] e ~f:(fun acc -> function
            | Lvar pv when List.exists parameters ~f:(fun (param, _) -> Pvar.equal param pv) ->
                (pv, klass) :: acc
            | _ ->
                acc )
      | _ ->
          [] )


  let construct_for_parameter ~parameter ~klass ~loc =
    let construct fields =
      let create_on_field (fn, _, annot) =
        create (MissingSideEffect (parameter, fn)) loc Sil.skip_instr []
        |> Option.some_if (not (Annot.Item.is_final annot))
      in
      List.filter_map fields ~f:create_on_field
    in
    match Program.Class.lookup !!pgm klass with
    | Some Struct.{java_class_info= Some {kind= Interface}} ->
        let fields =
          List.concat_map
            ~f:(fun impl ->
              Option.value_map (Program.Class.lookup !!pgm impl) ~default:[]
                ~f:(fun Struct.{fields} -> fields) )
            (Program.Class.find_impl !!pgm klass)
          |> List.dedup_and_sort ~compare:Struct.compare_field
        in
        construct fields
    | Some Struct.{fields} ->
        construct fields
    | _ ->
        []


  let construct_for_array_parameter proc ~loc =
    let array_fn = Fieldname.make (Typ.Name.Java.from_string "FL4APR_DUMMY_CLASS") "*" in
    let make_fault pv = create (MissingSideEffect (pv, array_fn)) loc Sil.skip_instr [] in
    let parameters = get_parameters !!pgm proc in
    List.filter_map parameters ~f:(fun (pv, typ) ->
        match Typ.(typ.desc) with
        | Tptr ({desc= Tarray _}, _) ->
            Some (make_fault pv)
        | Tarray _ ->
            Some (make_fault pv)
        | _ ->
            None )


  let enumerate location =
    if Program.CFG.is_switch_location location then []
    else
      let nodes_at_location = Program.find_node_with_location !!pgm location in
      let first = first_inter_node_at_location location in
      let on_plain_cfg =
        let nodes_at_location =
          (* there could be multiple procedure for the same location *)
          List.filter nodes_at_location ~f:(fun (proc, _) ->
              Procname.equal proc (InterNode.get_proc_name first) )
        in
        let loaded_parameters_at_location =
          List.concat_map nodes_at_location ~f:loaded_parameters_on
        in
        List.concat_map
          ~f:(fun (parameter, klass) ->
            construct_for_parameter ~parameter ~klass ~loc:(Before (first_instr_node first)) )
          loaded_parameters_at_location
        (* @ construct_for_array_parameter (InterNode.get_proc_name first) ~loc:(Before (first_instr_node first)) *)
      in
      let is_return_node n =
        Instrs.exists
          ~f:(function Sil.Store {e1= Lvar pv} when Pvar.is_return pv -> true | _ -> false)
          (InterNode.get_instrs n)
      in
      let on_return_node =
        match List.find nodes_at_location ~f:is_return_node with
        | Some node ->
            let parameters =
              Procdesc.get_pvar_formals (Program.pdesc_of !!pgm (InterNode.get_proc_name node))
              |> List.filter ~f:(fun (_, typ) -> Typ.is_pointer typ)
            in
            List.concat_map
              ~f:(fun (parameter, typ) ->
                let klass = Option.value_exn Typ.(name (strip_ptr typ)) in
                construct_for_parameter ~parameter ~klass ~loc:(Before (first_instr_node node)) )
              parameters
        | _ ->
            []
      in
      on_plain_cfg @ on_return_node
end

module ShouldSkip = struct
  let make_skip l_from l_to = create ShouldSkip (Range (l_from, l_to)) Sil.skip_instr []

  let instr_node_of n = InterNode.pnode_of n |> InstrNode.list_of_pnode

  let make_single_statement_skip (Location.{line; file} as location) =
    match Utils.read_file (SourceFile.to_abs_path file) with
    | Ok lines when Int.( >= ) (List.length lines) line ->
        let code_at_location = List.nth_exn lines (line - 1) in
        if String.is_suffix code_at_location ~suffix:";" then
          let first_instr_node =
            location |> first_inter_node_at_location |> instr_node_of |> List.hd_exn
          in
          let last_instr_node =
            location |> last_inter_node_at_location |> instr_node_of |> List.last_exn
          in
          if is_retnode (InstrNode.pnode_of last_instr_node) then None
          else if InstrNode.is_exit last_instr_node then None
          else Some (make_skip (Before first_instr_node) (After last_instr_node))
        else None
    | _ ->
        None


  let make_block_skip location =
    let node = first_inter_node_at_location location in
    match Program.CFG.find_outer_block_node !!pgm node with
    | Some outer_node when not (InterNode.is_exit outer_node) ->
        Some
          (make_skip
             (Before (instr_node_of node |> List.hd_exn))
             (Before (instr_node_of outer_node |> List.hd_exn)) )
    | _ ->
        None


  let enumerate location =
    List.filter_opt [make_single_statement_skip location; make_block_skip location]
end

let enumerate (score, location) =
  let enumerators =
    [ WrongExp.enumerate
    ; MissingSideEffect.enumerate
    ; MissingErrorHandling.enumerate
    ; ShouldSkip.enumerate ]
  in
  if is_testfile_str (Location.(location.file) |> SourceFile.to_rel_path) then []
  else
    List.concat_map enumerators ~f:(fun enum ->
        try List.map ~f:(fun f -> f ~score) (enum location) with _ -> [] )


let is_hole = Hole.is_hole

let description_name {desc} =
  match desc with
  | WrongExp _ ->
      "WrongExp"
  | MissingSideEffect _ ->
      "MissingSideEffect"
  | MissingErrorHandling _ ->
      "MissingErrorHandling"
  | ShouldSkip ->
      "ShouldSkip"


let id_of ({loc; desc} as fault) =
  let Location.{file; line} = get_location_node loc |> InstrNode.get_loc in
  let source = SourceFile.to_abs_path file |> String.split ~on:'/' |> List.last_exn in
  F.asprintf "%s:%d_%a_%x" source line pp_desc desc (Hashtbl.hash fault)


let exists_exn_sat {status} = match status with ExistExnSat -> true | _ -> false

let set_redundant fault = fault.is_redundant <- true

let pp_list ?(with_sort = true) fmt abs_patches =
  let abs_patches =
    if with_sort then
      List.sort abs_patches ~compare:(fun f1 f2 ->
          Int.of_float (f2.score *. 1000000.0) - Int.of_float (f1.score *. 1000000.0) )
    else abs_patches
  in
  F.fprintf fmt "%a" (Pp.seq ~sep:"\n" (Pp.of_string ~f:id_of)) abs_patches


module PrintableOrderedFault = struct
  type nonrec t = t [@@deriving compare]

  let pp = pp
end

module Set = PrettyPrintable.MakePPSet (PrintableOrderedFault)
module Map = PrettyPrintable.MakePPMap (PrintableOrderedFault)
