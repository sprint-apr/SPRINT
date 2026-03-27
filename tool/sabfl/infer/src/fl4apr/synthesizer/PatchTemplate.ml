open! IStd
open! Vocab
module AE = ASTExp
module Node = Fault.Node
module Method = Procname.Java

type t = {name: string; generate: Fault.t -> Patch.t list}

module Utils = struct
  let pgm = lazy (Program.from_marshal ())

  let ( let* ) = IOption.Let_syntax.( let* )

  let ( and+ ) = IOption.Let_syntax.( and+ )

  let ( let+ ) = IOption.Let_syntax.( let+ )

  let ( let@ ) x f = Option.value_map ~f ~default:[] x

  let get_loaded_access_expr node =
    match InstrNode.get_instr node with
    | Sil.Load {id; e} ->
        let pdesc = Program.pdesc_of !!pgm (InstrNode.get_proc_name node) in
        ( and+ ) (Some id) (ASTExp.from_IR_exp_opt pdesc e)
    | _ ->
        None


  let method_has_same_signature_with mthd pd =
    let open Procname in
    match Procdesc.get_proc_name pd with
    | Java mthd' when String.equal (Java.get_method mthd) (Java.get_method mthd') -> (
        let ret_ty, ret_ty' = (Java.get_return_typ mthd, Java.get_return_typ mthd') in
        let params, params' = (Java.get_parameters mthd, Java.get_parameters mthd') in
        match
          List.for_all2 (ret_ty :: params) (ret_ty' :: params') ~f:(fun p1 p2 -> Typ.equal p1 p2)
        with
        | Ok true ->
            true
        | _ ->
            false )
    | _ ->
        false


  let find_sibling_classes_by_predicate ~cls ~pred =
    List.filter (Program.Class.find_siblings !!pgm cls) ~f:pred


  type invoked_method_info = {base: AE.base; mthd: Procname.Java.t; args: AE.t list}

  let get_invoked_method_info pdesc e_org : invoked_method_info option =
    match ASTExp.from_IR_exp_opt pdesc e_org with
    | Some (MethodCall {base; mthd_hole= Filled mthd; args_hole= Some args}) ->
        Some {base; mthd; args}
    | _ ->
        None
end

let templates : t list ref = ref []

let abstract_templates : t list ref = ref []

module EGenRule = struct
  type t = {typ: Typ.t; gen_subterms: Procname.Java.t -> AE.t list; construct: AE.t list -> AE.t}

  let equality =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.any_primitive_type_hole; AE.any_primitive_type_hole])
    ; construct= (fun terms -> AE.Binary (Binop.Eq, List.nth_exn terms 0, List.nth_exn terms 1)) }


  let inequality =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.Hole Typ.int; AE.Hole Typ.int])
    ; construct= (fun terms -> AE.Binary (Binop.Lt, List.nth_exn terms 0, List.nth_exn terms 1)) }


  let null_check =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.object_hole; AE.null])
    ; construct= (fun terms -> AE.Binary (Binop.Eq, List.nth_exn terms 0, List.nth_exn terms 1)) }


  let non_null_check =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.object_hole; AE.null])
    ; construct= (fun terms -> AE.Binary (Binop.Ne, List.nth_exn terms 0, List.nth_exn terms 1)) }


  let logical_or =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.Hole Typ.boolean; AE.Hole Typ.boolean])
    ; construct= (fun terms -> AE.Binary (Binop.LOr, List.nth_exn terms 0, List.nth_exn terms 1)) }


  let neg =
    { typ= Typ.boolean
    ; gen_subterms= (fun _ -> [AE.Hole Typ.boolean])
    ; construct= (fun terms -> AE.Unary (Unop.LNot, List.nth_exn terms 0)) }


  let rules : t list = [equality; inequality; null_check; non_null_check; logical_or; neg]

  let apply_rules_transitively (mthd : Procname.Java.t) e =
    (* TODO: apply rules transitively *)
    let open AE in
    let onestep = function
      | Hole ty ->
          List.filter_map
            ~f:(fun {typ; gen_subterms; construct} ->
              Option.some_if (Typ.equal typ ty) (construct (gen_subterms mthd)) )
            rules
      | e ->
          [e]
    in
    onestep e


  let enumerate ?(max_cost = Config.sprint_synthesizer_max_search_depth) mthd e =
    let templates = e :: apply_rules_transitively (Procname.as_java_exn ~explanation:"" mthd) e in
    List.concat_map
      ~f:(fun e' -> Enumerator.enum_expressions ~initial_expression:e' ~max_cost mthd)
      templates
end

type common_context =
  {node: Fault.Node.t; method_name: Procname.t; pdesc: Procdesc.t; loc: Fault.location}

let register ~abstract ~name ~matcher ~generate_patches =
  let generate Fault.{loc; desc} =
    let common_context =
      let node = Fault.get_location_node loc in
      let method_name = InstrNode.get_proc_name node in
      let pdesc = Program.pdesc_of (Program.from_marshal ()) method_name in
      {node; method_name; pdesc; loc}
    in
    match matcher (desc, common_context) with
    | Some context ->
        generate_patches common_context context
        |> List.map ~f:(fun kind -> Patch.mk ~location:loc ~kind)
    | None ->
        []
  in
  let template = {name; generate} in
  if abstract then abstract_templates := template :: !abstract_templates
  else templates := template :: !templates ;
  template


let make_exp_replace_template ~abstract ~name
    ~(enumerator : common_context -> Exp.t * Typ.t -> AE.t list) =
  let matcher = function Fault.WrongExp (e_org, e_typ), _ -> Some (e_org, e_typ) | _ -> None in
  let generate_patches ({method_name} as common_context) (e_org, e_typ) =
    let expressions =
      List.concat_map (enumerator common_context (e_org, e_typ)) ~f:(EGenRule.enumerate method_name)
    in
    List.map expressions ~f:(fun e_rep -> Patch.Kind.ExpReplacement {e_org; e_rep; ty_org= e_typ})
  in
  register ~abstract ~name ~matcher ~generate_patches


(*********************************
  *** concrete patch templates ***
  ********************************)
let replace_with_new_expression =
  let enumerator _ (_, e_typ) = [AE.Hole e_typ] in
  make_exp_replace_template ~abstract:false ~name:"ReplaceWholeExpression" ~enumerator


let mutate_cast_expression =
  let primitive_types =
    List.map Typ.[FDouble; FFloat] ~f:(fun fk -> Typ.mk (Tfloat fk))
    @ List.map Typ.[IChar; IShort; IInt; ILong] ~f:(fun ik -> Typ.mk (Tint ik))
  in
  let matcher = function
    | Fault.WrongExp (Cast _, _), _ ->
        None
    | Fault.WrongExp (e_org, e_typ), {node}
      when List.mem primitive_types ~equal:Typ.equal e_typ
           && List.exists
                (Sil.exps_of_instr (Node.get_instr node))
                ~f:(function Exp.BinOp _ | Exp.Cast (_, Exp.BinOp _) -> true | _ -> false) ->
        Some (e_org, e_typ)
    | _ ->
        None
  in
  let generate_patches _ (e_match, e_typ) =
    List.filter_map primitive_types ~f:(fun ty_to ->
        Option.some_if
          (not (Typ.equal ty_to e_typ))
          (Patch.Kind.MutateCastingType {e_match; ty_org= e_typ; ty_to}) )
  in
  register ~abstract:false ~name:"MutateCastingType" ~matcher ~generate_patches


let invoke_method_with_variable_argument =
  let enumerator {pdesc} (e_org, e_typ) =
    match ASTExp.from_IR_exp_opt pdesc e_org with
    | Some (ASTExp.Var (pv, _)) when not (Pvar.is_frontend_tmp pv || Pvar.is_this pv) ->
        let open AE in
        [ MethodCall
            { base= DynamicAccess (Hole Typ.pointer_to_java_lang_object)
            ; mthd_hole= Empty e_typ
            ; args_hole= Some [of_var (pv, e_typ)] }
        ; MethodCall
            { base= StaticAccess any_type_component_hole
            ; mthd_hole= Empty e_typ
            ; args_hole= Some [of_var (pv, e_typ)] } ]
    | _ ->
        []
  in
  make_exp_replace_template ~abstract:false ~name:"InvokedMethodWithVariableArgument" ~enumerator


let mutate_base_variable_of_invocation =
  let enumerator {pdesc} (e_org, _) =
    match AE.from_IR_exp_opt pdesc e_org with
    | Some (MethodCall ({base= DynamicAccess (Var (base, ty_base))} as mc)) ->
        let vars =
          Collector.Variables.collect
            ~pred:(fun (pv, ty) -> (not (Pvar.equal base pv)) && Typ.equal ty_base ty)
            (Procdesc.get_proc_name pdesc)
        in
        List.map vars ~f:(fun (pv, ty) ->
            AE.MethodCall {mc with base= DynamicAccess (AE.Var (pv, ty))} )
    | _ ->
        []
  in
  make_exp_replace_template ~abstract:false ~name:"MutateBaseVariableOfInvocation" ~enumerator


let invoke_overloaded_method =
  let open Utils in
  let enumerator {pdesc} (e_org, _) =
    let@ {base; mthd; args} = get_invoked_method_info pdesc e_org in
    let params = Method.get_parameters mthd in
    let punch_method mthd' =
      let params' = Method.get_parameters mthd' in
      let punch at =
        let args' =
          match at with
          | `Pre ->
              AE.Hole (List.hd_exn params') :: args
          | `Post ->
              args @ [AE.Hole (List.last_exn params')]
        in
        AE.MethodCall {base; mthd_hole= Filled mthd'; args_hole= Some args'}
      in
      List.filter_opt
        [ Option.some_if (List.is_suffix params' ~suffix:params ~equal:Typ.equal) (punch `Pre)
        ; Option.some_if (List.is_prefix params' ~prefix:params ~equal:Typ.equal) (punch `Post) ]
    in
    Program.find_overloaded_methods !!pgm mthd
    |> List.filter ~f:(fun mthd' ->
           Int.equal (List.length params + 1) (List.length (Method.get_parameters mthd')) )
    |> List.concat_map ~f:punch_method
  in
  make_exp_replace_template ~abstract:false ~name:"InvokeOverloadedMethod" ~enumerator


let mutate_invoked_method =
  let open Utils in
  let enumerator {pdesc} (e_org, _) =
    let@ {base; mthd; args} = get_invoked_method_info pdesc e_org in
    [AE.MethodCall {base; mthd_hole= Empty (AE.Ty.get_return_type mthd); args_hole= Some args}]
  in
  make_exp_replace_template ~abstract:false ~name:"MutateInvokedMethod" ~enumerator


let mutate_operator =
  let open Utils in
  let arithmetics = Binop.[PlusA None; MinusA None; Mult None; Div] in
  let relationals = Binop.[Lt; Gt; Le; Ge] in
  let get_same_class_bos bo =
    if List.mem ~equal:Binop.equal arithmetics bo then arithmetics
    else if List.mem ~equal:Binop.equal relationals bo then relationals
    else []
  in
  let enumerator {pdesc} (e_org, _) =
    let@ ae = AE.from_IR_exp_opt pdesc e_org in
    let rec f ae =
      match (ae : AE.t) with
      | Unary (_, e') ->
          f e'
      | Binary (bo, lhs, rhs) ->
          List.map (get_same_class_bos bo) ~f:(fun bo' -> AE.Binary (bo', lhs, rhs))
          @ List.map (f rhs) ~f:(fun rhs' -> AE.Binary (bo, lhs, rhs'))
      | _ ->
          []
    in
    f ae
  in
  make_exp_replace_template ~abstract:false ~name:"MutateOperator" ~enumerator


let mutate_arithmetic_operation_priority =
  let is_plus_or_minus = function Binop.PlusA _ | MinusA _ -> true | _ -> false in
  let is_mult_or_div = function Binop.Mult _ | Div -> true | _ -> false in
  let enumerator {pdesc} (e_org, _) =
    let open AE in
    match from_IR_exp_opt pdesc e_org with
    | Some (Binary (bo1, Binary (bo2, x, y), z))
      when (is_plus_or_minus bo1 && is_mult_or_div bo2)
           || (is_mult_or_div bo2 && is_plus_or_minus bo1) ->
        [Binary (bo1, x, Binary (bo2, y, z))]
    | Some (Binary (bo1, x, Binary (bo2, y, z)))
      when (is_plus_or_minus bo1 && is_mult_or_div bo2)
           || (is_mult_or_div bo2 && is_plus_or_minus bo1) ->
        [Binary (bo1, Binary (bo2, x, y), z)]
    | _ ->
        []
  in
  make_exp_replace_template ~abstract:false ~name:"MutateArithmeicOperationPriority" ~enumerator


let mutate_condition =
  let enumerator {pdesc; node; method_name} (e_org, e_typ) =
    let is_prune_node =
      match InterNode.get_kind node.inode with Procdesc.Node.Prune_node _ -> true | _ -> false
    in
    let rec f = function
      | Exp.UnOp (_, e', _) ->
          f e'
      | Exp.BinOp _ as e when is_prune_node && Typ.equal e_typ Typ.boolean -> (
        try
          let ae_org = AE.from_IR_exp pdesc e in
          let new_conds = EGenRule.enumerate method_name (AE.Hole Typ.boolean) in
          List.cartesian_product [Binop.LAnd; Binop.LOr] new_conds
          |> List.map ~f:(fun (bo', e') -> AE.Binary (bo', e', ae_org))
        with _ -> [] )
      | _ ->
          []
    in
    f e_org
  in
  make_exp_replace_template ~abstract:false ~name:"MutateCondition" ~enumerator


let mutate_var_decl_type =
  let open Utils in
  let primitive_types =
    List.map Typ.[FDouble; FFloat] ~f:(fun fk -> Typ.mk (Tfloat fk))
    @ List.map Typ.[IChar; IShort; IInt; ILong] ~f:(fun ik -> Typ.mk (Tint ik))
  in
  let matcher (desc, {node; pdesc}) =
    let* typ =
      match desc with
      | Fault.WrongExp (_, (Typ.{desc= Tint _ | Tfloat _} as t))
        when List.mem primitive_types t ~equal:Typ.equal_ignore_quals ->
          Some t
      | _ ->
          None
    in
    match (InstrNode.get_instr node : Sil.instr) with
    | (Load {e= Lvar pvar} | Store {e1= Lvar pvar}) when not (Pvar.is_frontend_tmp pvar) ->
        let* decl_loc =
          let sorted_nodes = Procdesc.get_nodes pdesc |> List.sort ~compare:Procdesc.Node.compare in
          List.find_map sorted_nodes ~f:(fun n ->
              Instrs.find_map (Procdesc.Node.get_instrs n) ~f:(function
                | Sil.Store {e1= Lvar pv; loc} when Pvar.equal pv pvar ->
                    Some loc
                | _ ->
                    None ) )
        in
        Some (pvar, typ, decl_loc)
    | _ ->
        None
  in
  let generate_patches _ (pvar, typ, decl_loc) =
    List.map primitive_types ~f:(fun ty' ->
        Patch.Kind.MutateVarDeclType {pvar; ty_from= typ; ty_to= ty'; decl_loc} )
  in
  register ~abstract:false ~name:"MutateVarDeclType" ~matcher ~generate_patches


let mutate_fraction_type =
  let open Utils in
  let enumerator {pdesc} (e_org, _) =
    match (e_org : Exp.t) with
    | BinOp (((Div | Mult _) as bo), lhs, rhs) ->
        let@ ae_lhs = AE.from_IR_exp_opt pdesc lhs in
        let@ ae_rhs = AE.from_IR_exp_opt pdesc rhs in
        [ AE.Binary (bo, AE.Cast (Typ.double, ae_lhs), ae_rhs)
        ; AE.Binary (bo, ae_lhs, AE.Cast (Typ.double, ae_rhs)) ]
    | _ ->
        []
  in
  make_exp_replace_template ~abstract:false ~name:"MutateFractionType" ~enumerator


let insert_return =
  let matcher = function
    | Fault.MissingErrorHandling `Return, {pdesc} ->
        let ty_ret = Procdesc.get_ret_type pdesc in
        Option.some_if (Typ.is_java_type ty_ret) ty_ret
    | _ ->
        None
  in
  let generate_patches {method_name} ret_typ =
    let conditions = EGenRule.enumerate method_name (AE.Hole Typ.boolean) in
    if Typ.is_void ret_typ then
      List.map conditions ~f:(fun cond -> Patch.Kind.InsertHandle {cond; hkind= Return None})
    else
      let returns = AE.default_of ret_typ in
      let cond_return_pairs = List.cartesian_product conditions returns in
      List.map cond_return_pairs ~f:(fun (cond, ret) ->
          Patch.Kind.InsertHandle {cond; hkind= Return (Some ret)} )
  in
  register ~abstract:false ~name:"InsertReturn" ~matcher ~generate_patches


let find_throw_constructors typ =
  let get_default_value_for_exn_args typ =
    let either_type_of types = List.mem ~equal:Typ.equal types typ in
    match typ with
    | _ when either_type_of [Typ.java_char; Typ.pointer_to_java_lang_string] ->
        Some (AE.Literal (String ""))
    | _
      when either_type_of
             [ Typ.int
             ; Typ.uint
             ; Typ.long
             ; Typ.mk_ptr (Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Number")) ] ->
        Some (AE.Literal (Integer IntLit.zero))
    | _ when either_type_of [Typ.float; Typ.double] ->
        Some (AE.Literal (Float 0.0))
    | _
      when either_type_of
             [Typ.boolean; Typ.mk_ptr (Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Bool"))]
      ->
        Some AE.lit_false
    | Typ.{desc= Tptr _} ->
        Some AE.null
    | _ ->
        None
  in
  let name = Option.value_exn (Typ.name typ) in
  let constructors =
    Program.find_methods_in_class ~find_library_methods:true !!Utils.pgm name
      ~pred:Procname.is_constructor
    |> Procname.Set.filter (function
         | Procname.Java mthd ->
             Procname.Java.get_class_type_name mthd |> Typ.Name.equal name
         | _ ->
             false )
  in
  if Procname.Set.is_empty constructors then []
  else
    let mthd = Procname.as_java_exn ~explanation:"" (Procname.Set.choose constructors) in
    let params = Procname.Java.get_parameters mthd in
    let args_converted = List.filter_map params ~f:get_default_value_for_exn_args in
    if Int.( = ) (List.length params) (List.length args_converted) then
      [ AE.MethodCall
          { base= StaticAccess (Filled (Procname.Java.get_class_type_name mthd))
          ; mthd_hole= Filled mthd
          ; args_hole= Some args_converted } ]
    else []


let insert_throw =
  let matcher = function
    | Fault.MissingErrorHandling (`Throw exn_typ), _ ->
        Some exn_typ
    | _ ->
        None
  in
  let generate_patches {method_name} exn_typ =
    let conditions = EGenRule.enumerate method_name (AE.Hole Typ.boolean) in
    let throws = find_throw_constructors exn_typ in
    let cond_throw_pairs = List.cartesian_product conditions throws in
    List.map cond_throw_pairs ~f:(fun (cond, exn) ->
        Patch.Kind.InsertHandle {cond; hkind= Throw exn} )
  in
  register ~abstract:false ~name:"InsertThrow" ~matcher ~generate_patches


module FieldnameComparator = struct
  include
    ( val Comparator.make ~compare:Fieldname.compare
            ~sexp_of_t:(Fieldname.to_string >>> Sexp.of_string) )

  type t = Fieldname.t
end

let inversed_side_effects_map =
  lazy
    (let open Program in
    SideEffects.bindings (side_effects !!Utils.pgm)
    |> List.concat_map ~f:(fun (proc, indexed_fields) ->
           if Procname.is_constructor proc then []
           else
             List.map (ParamFields.elements indexed_fields) ~f:(fun (idx, fn) -> (fn, (proc, idx))) )
    |> Map.of_alist_multi (module FieldnameComparator) )


let insert_method_call =
  let matcher = function
    | Fault.MissingSideEffect (pvar, fn), {pdesc} when not (Pvar.is_frontend_tmp pvar) ->
        let ProcAttributes.{formals; locals} = Procdesc.get_attributes pdesc in
        let ty_pv =
          List.find_map_exn
            ~f:(fun (name, ty) -> if Mangled.equal name (Pvar.get_name pvar) then Some ty else None)
            (formals @ List.map locals ~f:(fun ProcAttributes.{name; typ} -> (name, typ)))
        in
        Some (pvar, ty_pv, fn)
    | _ ->
        None
  in
  let generate_patches {method_name} ((base : Pvar.t), (ty_base : Typ.t), fn) =
    let procs_mutate_fn = Map.find_multi !!inversed_side_effects_map fn in
    let calls =
      if List.is_empty procs_mutate_fn then
        Enumerator.enum_expressions
          ~initial_expression:
            (AE.MethodCall
               { base= DynamicAccess (AE.of_var (base, ty_base))
               ; mthd_hole= AE.any_type_component_hole
               ; args_hole= None } )
          ~max_cost:(Config.sprint_synthesizer_max_search_depth - 1)
          method_name
      else
        List.filter_map procs_mutate_fn ~f:(fun (proc, idx) ->
            let pvar_formals = Procdesc.get_pvar_formals (Option.value_exn (Procdesc.load proc)) in
            let _, ty_idx = List.nth_exn pvar_formals idx in
            let mthd = Procname.as_java_exn ~explanation:"" proc in
            if Procname.Java.is_static mthd then None
            else
              let base, args_hole =
                let[@warning "-8"] [(_, ty_this)], pvar_formals = List.split_n pvar_formals 1 in
                ( AE.DynamicAccess (if Int.equal idx 0 then AE.Var (base, ty_idx) else Hole ty_this)
                , List.mapi pvar_formals ~f:(fun i (_, ty) ->
                      if Int.equal i (idx - 1) then AE.Var (base, ty_base) else AE.Hole ty ) )
              in
              if List.count args_hole ~f:(function AE.Hole _ -> true | _ -> false) > 1 then None
              else Some (AE.MethodCall {base; mthd_hole= Filled mthd; args_hole= Some args_hole}) )
        |> List.concat_map ~f:(fun initial_expression ->
               Enumerator.enum_expressions ~initial_expression
                 ~max_cost:(Config.sprint_synthesizer_max_search_depth - 1)
                 method_name )
    in
    List.map calls ~f:(fun call -> Patch.Kind.InsertMethodCall {method_call= call})
  in
  register ~abstract:false ~name:"InsertMethodCall" ~matcher ~generate_patches


let skip_matcher = function
  | Fault.ShouldSkip, {loc= Range (Before n1, After n2)}
    when Location.equal (Node.get_loc n1) (Node.get_loc n2) ->
      Some false
  | Fault.ShouldSkip, {loc= Range (Before _, Before n2)} ->
      let is_loop_node =
        let loop_pattern = Str.regexp "[ \t]*\(while\|for\)[ \t]?(" in
        let loc = Node.get_loc n2 in
        Str.string_match loop_pattern (read_source_location loc) 0
        || Str.string_match loop_pattern
             (read_source_location Location.{loc with line= loc.line - 1})
             0
      in
      Some is_loop_node
  | _ ->
      None


let skip_stmt =
  let generate_patches {method_name} is_continue =
    let conds = EGenRule.enumerate method_name (AE.Hole Typ.boolean) in
    List.map conds ~f:(fun cond -> Patch.Kind.SkipStmt {cond; is_continue})
  in
  register ~abstract:false ~name:"SkipStmt" ~matcher:skip_matcher ~generate_patches


(*********************************
  *** abstract patch templates ***
  ********************************)
let abstract_replace_with_new_expression =
  let enumerator _ (_, _) = [AE.mask_token] in
  make_exp_replace_template ~abstract:true ~name:"ReplaceWholeExpression" ~enumerator


(** This template seems less useful if patches are inferenced by llm **)
(* let abstract_mutate_cast_expression =
   let primitive_types =
     List.map Typ.[FDouble; FFloat] ~f:(fun fk -> Typ.mk (Tfloat fk))
     @ List.map Typ.[IChar; IShort; IInt; ILong] ~f:(fun ik -> Typ.mk (Tint ik))
   in
   let matcher = function
     | Fault.WrongExp (Cast _, _), _ ->
         None
     | Fault.WrongExp (e_org, e_typ), {node}
       when List.mem primitive_types ~equal:Typ.equal e_typ
            && List.exists
                 (Sil.exps_of_instr (Node.get_instr node))
                 ~f:(function Exp.BinOp _ | Exp.Cast (_, Exp.BinOp _) -> true | _ -> false) ->
         Some (e_org, e_typ)
     | _ ->
         None
   in
   let generate_patches _ (e_match, e_typ) =
     [Patch.Kind.MutateCastingType {e_match; ty_org= e_typ; ty_to= AE.Ty.any_type}]
   in
   register ~abstract:true ~name:"MutateCastingType" ~matcher ~generate_patches *)

let abstract_insert_return =
  let matcher = function
    | Fault.MissingErrorHandling `Return, {pdesc} ->
        Some (Procdesc.get_ret_type pdesc)
    | _ ->
        None
  in
  let generate_patches _ ret_typ =
    [ Patch.Kind.InsertHandle
        { cond= AE.mask_token
        ; hkind= Return (Option.some_if (not (Typ.is_void ret_typ)) AE.mask_token) } ]
  in
  register ~abstract:true ~name:"InsertReturn" ~matcher ~generate_patches


let abstract_insert_throw =
  let matcher = function
    | Fault.MissingErrorHandling (`Throw exn_typ), _ ->
        Some exn_typ
    | _ ->
        None
  in
  let generate_patches _ exn_typ =
    let conditions = [AE.mask_token] in
    let throws = find_throw_constructors exn_typ in
    let cond_throw_pairs = List.cartesian_product conditions throws in
    List.map cond_throw_pairs ~f:(fun (cond, exn) ->
        Patch.Kind.InsertHandle {cond; hkind= Throw exn} )
  in
  register ~abstract:true ~name:"InsertThrow" ~matcher ~generate_patches


let abstract_skip_stmt =
  let generate_patches _ is_continue =
    let conds = [AE.mask_token] in
    List.map conds ~f:(fun cond -> Patch.Kind.SkipStmt {cond; is_continue})
  in
  register ~abstract:true ~name:"SkipStmt" ~matcher:skip_matcher ~generate_patches


let abstract_mutate_var_decl_type =
  let open Utils in
  let primitive_types =
    List.map Typ.[FDouble; FFloat] ~f:(fun fk -> Typ.mk (Tfloat fk))
    @ List.map Typ.[IChar; IShort; IInt; ILong] ~f:(fun ik -> Typ.mk (Tint ik))
  in
  let matcher (desc, {node; pdesc}) =
    let* typ =
      match desc with
      | Fault.WrongExp (_, (Typ.{desc= Tint _ | Tfloat _} as t))
        when List.mem primitive_types t ~equal:Typ.equal_ignore_quals ->
          Some t
      | _ ->
          None
    in
    match (InstrNode.get_instr node : Sil.instr) with
    | (Load {e= Lvar pvar} | Store {e1= Lvar pvar}) when not (Pvar.is_frontend_tmp pvar) ->
        let* decl_loc =
          let sorted_nodes = Procdesc.get_nodes pdesc |> List.sort ~compare:Procdesc.Node.compare in
          List.find_map sorted_nodes ~f:(fun n ->
              Instrs.find_map (Procdesc.Node.get_instrs n) ~f:(function
                | Sil.Store {e1= Lvar pv; loc} when Pvar.equal pv pvar ->
                    Some loc
                | _ ->
                    None ) )
        in
        Some (pvar, typ, decl_loc)
    | _ ->
        None
  in
  let generate_patches _ (pvar, typ, decl_loc) =
    [Patch.Kind.MutateVarDeclType {pvar; ty_from= typ; ty_to= AE.Ty.any_type; decl_loc}]
  in
  register ~abstract:true ~name:"MutateVarDeclType" ~matcher ~generate_patches


let abstract_insert_call =
  let matcher = function
    | Fault.MissingSideEffect (pvar, _), {pdesc} when not (Pvar.is_frontend_tmp pvar) ->
        AE.from_IR_exp_opt pdesc (Exp.Lvar pvar)
    | _ ->
        None
  in
  let generate_patches _ (base : AE.t) =
    let pvar_base_call =
      AE.(MethodCall {base= DynamicAccess base; mthd_hole= Empty Typ.void; args_hole= None})
    in
    let pvar_arg_call =
      AE.(
        MethodCall
          {base= StaticAccess (Empty Typ.void); mthd_hole= Empty Typ.void; args_hole= Some [base]} )
    in
    List.map [pvar_base_call; pvar_arg_call] ~f:(fun call ->
        Patch.Kind.InsertMethodCall {method_call= call} )
  in
  register ~abstract:true ~name:"InsertAbstractCall" ~matcher ~generate_patches


(** This template seems less useful if patches are inferenced by llm **)
(* let abstract_mutate_condition =
   let enumerator {pdesc; node; _} (e_org, e_typ) =
     let is_prune_node =
       match InterNode.get_kind node.inode with Procdesc.Node.Prune_node _ -> true | _ -> false
     in
     let rec f = function
       | Exp.UnOp (_, e', _) ->
           f e'
       | Exp.BinOp _ as e when is_prune_node && Typ.equal e_typ Typ.boolean -> (
         try
           let ae_org = AE.from_IR_exp pdesc e in
           let new_conds = [AE.mask_token] in
           List.cartesian_product [Binop.LAnd; Binop.LOr] new_conds
           |> List.map ~f:(fun (bo', e') -> AE.Binary (bo', e', ae_org))
         with _ -> [] )
       | _ ->
           []
     in
     f e_org
   in
   make_exp_replace_template ~abstract:true ~name:"AbstractMutateCondition" ~enumerator *)

let abstract_replace_line =
  let matcher _ = Some () in
  let generate_patches _ _ = [Patch.Kind.ReplaceLine] in
  register ~abstract:true ~name:"ReplaceLine" ~matcher ~generate_patches


let abstract_insert_line =
  let matcher _ = Some () in
  let generate_patches _ _ = [Patch.Kind.InsertLine] in
  register ~abstract:true ~name:"InsertLine" ~matcher ~generate_patches


let get_templates () = !templates

let get_abstract_templates () = !abstract_templates
