open! IStd
open! Vocab
open! Comby
module F = Format
module AE = ASTExp

let pgm = lazy (Program.from_marshal ())

let metasyntax = Matchers.Metasyntax.default_metasyntax

type application = {cmd: string; result: (replacement, string) Result.t}

and replacement = {rewritten_source: string; matched_part: string}

let java_matcher =
  Option.value_exn
    (Matchers.Alpha.select_with_extension ~metasyntax:Matchers.Metasyntax.default_metasyntax
       ("." ^ "java") )


type matching_context = {match_template: string; source_path: string; line: int}

let pp_matching_context fmt {match_template; source_path; line} =
  F.fprintf fmt "<%s, %s, %d>" match_template source_path line


module Hashtbl = Caml.Hashtbl

let comby_match_tbl : (matching_context, (match', string) Result.t list) Hashtbl.t =
  Hashtbl.create 1214


type instruction =
  | Comby of {match_template: string; rewrite_template: string; source_path: string; line: int}
  | Sed of {rewrite_template: string; source_path: string; line: int}

let instruction_to_string = function
  | Comby {match_template; rewrite_template; source_path} ->
      F.asprintf "cat %s | comby -matcher .java \"%s\" \"%s\" -stdin" source_path match_template
        rewrite_template
  | Sed {rewrite_template; source_path; line} ->
      F.asprintf "sed '%dc%s' %s " line rewrite_template source_path


let _read_line_cache = ref String.Map.empty

let read_lines source_path =
  match String.Map.find !_read_line_cache source_path with
  | Some lines ->
      lines
  | None ->
      let result = In_channel.read_lines source_path in
      _read_line_cache := String.Map.add_exn ~key:source_path ~data:result !_read_line_cache ;
      result


let rec match_expression ?(ty_opt = None) ?(in_binary_operand = false) ~source_path ~line
    ~line_to_match scope e =
  let match_expression = match_expression ~line_to_match ~line ~source_path in
  let ty = Option.value_map ty_opt ~default:(AE.typeof e) ~f:(fun x -> x) in
  match (e : AE.t) with
  | Hole _ ->
      L.die InternalError "matching hole expression is invalid"
  | Var (pv, _) ->
      [Pvar.to_string pv]
  | Literal lit ->
      match_literal lit ~ty
  | Cast (Typ.{desc= Tstruct name}, e) ->
      let unqualified_name =
        String.split_on_chars (Typ.Name.name name) ~on:['.'] |> List.rev |> List.hd_exn
      in
      List.map
        ~f:(F.asprintf "(%s):[~ ?]%s" unqualified_name)
        (match_expression scope e ~in_binary_operand)
  | Cast (_, Cast (ty, e)) ->
      List.map
        ~f:(F.asprintf "(%s):[~ ?]%s" (Typ.to_string ty))
        (match_expression scope e ~in_binary_operand)
  | Cast (ty, e) ->
      List.map
        ~f:(F.asprintf "(%s):[~ ?]%s" (Typ.to_string ty))
        (match_expression scope e ~in_binary_operand)
  | Unary ((Unop.Neg as neg), e) ->
      List.map
        ~f:(F.asprintf "%s:[~\\(?]%s:[~\\)?]" (Unop.to_string neg))
        (match_expression scope e)
  | Unary (_, e) ->
      match_expression scope e
  | Binary (((Binop.Eq | Binop.Ne | Binop.Le | Binop.Lt | Binop.Ge | Binop.Gt) as bo), lhs, rhs) ->
      (* Equalities *)
      let lhs_matches, rhs_matches =
        ( match_expression scope lhs ~in_binary_operand:true
        , match_expression scope rhs ~in_binary_operand:true )
      in
      let plain_binaries =
        List.map
          ~f:(fun (h_lhs, h_rhs) -> F.asprintf "%s %s %s" h_lhs (Binop.str Pp.text bo) h_rhs)
          (List.cartesian_product lhs_matches rhs_matches)
      in
      let unaries =
        match bo with
        | Binop.Eq when (not (AE.is_null rhs)) && AE.is_zero rhs ->
            List.map lhs_matches ~f:(F.asprintf "!%s")
        | Binop.Ne when (not (AE.is_null rhs)) && AE.is_zero rhs ->
            List.map lhs_matches ~f:(F.asprintf "%s")
        | _ ->
            []
      in
      unaries @ plain_binaries
  | Binary (_, lhs, rhs) ->
      (* Arithmetics, Relationals ... *)
      let lhs_matches, rhs_matches =
        ( match_expression scope lhs ~in_binary_operand:true
        , match_expression scope rhs ~in_binary_operand:true )
      in
      let results =
        List.map
          ~f:(fun (h_lhs, h_rhs) -> F.asprintf "%s :[_:e] %s" h_lhs h_rhs)
          (List.cartesian_product lhs_matches rhs_matches)
      in
      if in_binary_operand then
        List.concat_map results ~f:(fun s ->
            let matches_of_s = match_comby s source_path line line_to_match in
            if List.for_all matches_of_s ~f:Result.is_error then [] else [s] )
        @ List.concat_map results ~f:(fun s ->
              let s' = F.asprintf "(%s)" s in
              let matches_of_s' = match_comby s source_path line line_to_match in
              if List.for_all matches_of_s' ~f:Result.is_error then [] else [s'] )
      else results
  | Ternary _ as e ->
      L.progress "Skipping matching ternary ASTExp: %a@." ASTExp.pp e ;
      []
  | NewArray {elt_typ} ->
      [F.asprintf "new %s[:[_]]" (Typ.to_string elt_typ)]
  | FieldAccess {base; field_hole= Filled fn} ->
      let base_matches = match_base base scope ~line_to_match ~line ~source_path in
      let field_string = Fieldname.get_field_name fn in
      List.map base_matches ~f:(fun b -> b ^ field_string)
  | MethodCall {mthd_hole= Filled mthd} when Procname.Java.is_constructor mthd ->
      [F.asprintf "new %s(:[_])" (Procname.Java.get_simple_class_name mthd)]
  | MethodCall {base; mthd_hole= Filled mthd} ->
      let base_matches = match_base base scope ~line_to_match ~line ~source_path in
      List.map base_matches ~f:(fun b -> F.asprintf "%s%s(:[_])" b (Procname.Java.get_method mthd))
  | ArrayAccess {arrexp; index= Literal (Integer intlit)} ->
      let arr_matches = match_expression scope arrexp in
      List.map arr_matches ~f:(fun arr -> F.asprintf "%s[%s]" arr (IntLit.to_string intlit))
  | ArrayAccess {arrexp; index} ->
      let arr_matches, index_matches =
        (match_expression scope arrexp, match_expression scope index)
      in
      List.map
        ~f:(fun (arr, index) -> F.asprintf "%s[%s]" arr index)
        (List.cartesian_product arr_matches index_matches)
  | e ->
      L.die InternalError "This case never happens (%a)" ASTExp.pp e


and match_base ~line_to_match ~line ~source_path base scope =
  match (base : AE.base) with
  | StaticAccess (Filled cname) ->
      [ ( match Procname.get_class_type_name scope with
        | Some klass when Typ.Name.equal klass cname ->
            ""
        | _ ->
            (cname |> Typ.Name.Java.get_java_class_name_exn |> JavaClassName.classname) ^ "." ) ]
  | DynamicAccess e ->
      if ASTExp.is_this e then [":[~(this.)?]"]
      else
        List.map ~f:(fun s -> s ^ ".") (match_expression ~line ~source_path ~line_to_match scope e)
  | _ ->
      L.die InternalError "Matching unfilled base never happens@."


and match_literal lit ~ty =
  match (lit : AE.Literal.t) with
  | Integer il when Typ.equal ty Typ.boolean ->
      if IntLit.isone il then ["true"] else ["false"]
  | Integer il ->
      let true_or_false =
        if IntLit.iszero il then ["false"] else if IntLit.isone il then ["true"] else []
      in
      let candidates =
        match IntLit.to_int il with
        | Some integer ->
            List.filter_opt
              [ Option.map (Char.of_int integer) ~f:(F.asprintf "'%s'" <<< Char.escaped)
              ; (* hex digits *)
                Some (F.sprintf "0x%x" integer |> String.lowercase)
              ; (* raw character *)
                Some (string_of_int integer) (* raw integer *) ]
            @ true_or_false
        | None ->
            []
      in
      (* static field access case added *)
      [":[~[A-Z][A-z|0-9]+].:[~[A-Z|_]+]"; F.asprintf ":[~%s]" (String.concat ~sep:"|" candidates)]
  | NULL ->
      ["null"]
  | String str ->
      [String.concat ["\""; str; "\""]]
  | Float f ->
      let f_str = string_of_float f in
      if String.length f_str >= 13 then [":[~[A-Z][A-z|0-9]+].:[~[A-Z|_]+]"]
      else [string_of_int (int_of_float f); F.asprintf ":[~%s\\.?[0-9]*[f|F|d|D]?]" f_str]
  | _ ->
      []


and extract_rewrite_instructions Patch.{kind; procname; source_location} =
  let Location.{file; line} = source_location in
  let source_path = SourceFile.to_rel_path file in
  match kind with
  | MutateCastingType {e_match; ty_org; ty_to} -> (
    match ASTExp.from_IR_exp_opt (Program.pdesc_of !!pgm procname) e_match with
    | Some ae_org ->
        let line_to_match = List.nth_exn (read_lines source_path) (line - 1) in
        let match_templates =
          match_expression ~ty_opt:(Some ty_org) procname ae_org ~source_path ~line ~line_to_match
        in
        List.map match_templates ~f:(fun match_template ->
            let rewrite_template =
              if Typ.equal ty_to AE.Ty.any_type then
                F.asprintf "((%a) %a)" AE.pp AE.mask_token AE.pp ae_org
              else F.asprintf "((%s) %a)" (Typ.to_string ty_to) AE.pp ae_org
            in
            Comby {match_template; rewrite_template; source_path; line} )
    | None ->
        [] )
  | ExpReplacement {e_org; e_rep; ty_org} -> (
    match ASTExp.from_IR_exp_opt (Program.pdesc_of !!pgm procname) e_org with
    (* Handling instanceof expression *)
    | Some (Binary (binop, _, AE.MethodCall {mthd_hole= Filled mthd}))
    | Some (Binary (binop, AE.MethodCall {mthd_hole= Filled mthd}, _))
      when Procname.equal (Procname.Java mthd) (Procname.Java AE.instanceof) ->
        let match_template =
          match binop with
          | Binop.Eq ->
              F.asprintf "!(:[_:e] instanceof :[_:e])"
          | _ ->
              F.asprintf ":[_:e] instanceof :[_:e]"
        in
        let rewriter_template = F.asprintf "%a" AE.pp e_rep in
        [Comby {match_template; rewrite_template= rewriter_template; source_path; line}]
    | Some (Binary (_, ae1, _) as ae_org) ->
        let lines = read_lines source_path in
        let line_to_match = List.nth_exn lines (line - 1) in
        let line_to_match' = List.nth_exn lines line in
        let line =
          if
            (not (String.is_substring ~substring:(ASTExp.to_string ae1) line_to_match))
            && String.is_substring ~substring:(ASTExp.to_string ae1) line_to_match'
          then line + 1
          else line
        in
        let line_to_match = List.nth_exn (read_lines source_path) (line - 1) in
        let match_templates =
          match_expression ~ty_opt:(Some ty_org) procname ae_org ~line_to_match ~line ~source_path
        in
        let rewrite_template = F.asprintf "%a" AE.pp e_rep in
        List.map match_templates ~f:(fun match_template ->
            Comby {match_template; rewrite_template; source_path; line} )
    | Some ae_org ->
        let line_to_match = List.nth_exn (read_lines source_path) (line - 1) in
        let match_templates =
          match_expression ~ty_opt:(Some ty_org) procname ae_org ~line_to_match ~line ~source_path
        in
        let rewrite_template = F.asprintf "%a" AE.pp e_rep in
        List.map match_templates ~f:(fun match_template ->
            Comby {match_template; rewrite_template; source_path; line} )
    | None ->
        [] )
  | MutateVarDeclType {pvar; ty_from; ty_to; decl_loc} ->
      let match_template =
        F.asprintf "%s %s = :[rhs]" (Typ.to_string ty_from) (Pvar.to_string pvar)
      in
      let rewrite_template =
        if Typ.equal ty_to AE.Ty.any_type then
          F.asprintf "%a %s = :[rhs]" AE.pp AE.mask_token (Pvar.to_string pvar)
        else F.asprintf "%s %s = :[rhs]" (Typ.to_string ty_to) (Pvar.to_string pvar)
      in
      [Comby {match_template; rewrite_template; source_path; line= decl_loc.Location.line}]
  | InsertHandle {cond; hkind= Throw e} ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "if (%a)\n\tthrow %a;" AE.pp cond AE.pp e in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | InsertHandle {cond; hkind= Return ret_opt} ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line =
        match ret_opt with
        | Some ret when AE.equal ret AE.mask_token ->
            (* Prefer to express the prompt with a single mask 
             * e.g., if (MASK) return MASK => if (MASK; *)
            F.asprintf "if (%a;" AE.pp cond
        | Some ret ->
            F.asprintf "if (%a)\n\treturn %a;" AE.pp cond AE.pp ret
        | None ->
            F.asprintf "if (%a)\n\treturn;" AE.pp cond
      in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | InsertMethodCall {method_call= AE.MethodCall {base= DynamicAccess base; mthd_hole= Empty _}} ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "%a.%a;" AE.pp base AE.pp AE.mask_token in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | InsertMethodCall
      {method_call= AE.MethodCall {base= StaticAccess _; mthd_hole= Empty _; args_hole= Some [base]}}
    ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "%a(%a);" AE.pp AE.mask_token AE.pp base in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | InsertMethodCall {method_call} ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "%a;" AE.pp method_call in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | SkipStmt {cond; is_continue= true} ->
      (* insert S; if (C) continue; 
       * NOTE: insert after the original line S *)
      let line = line + 1 in
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "if (%a) continue;" AE.pp cond in
      let rewrite_template = F.asprintf "%s\n%s" matched_part insert_line in
      [Sed {rewrite_template; source_path; line}]
  | SkipStmt {cond; is_continue= false} ->
      (* insert if (C) S; 
       * NOTE: insert before the original line S *)
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let insert_line = F.asprintf "if (%a)\n" AE.pp cond in
      let rewrite_template = F.asprintf "%s\n%s" insert_line matched_part in
      [Sed {rewrite_template; source_path; line}]
  | ReplaceLine ->
      let rewrite_template = F.asprintf "%a" AE.pp AE.mask_token in
      [Sed {rewrite_template; source_path; line}]
  | InsertLine ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      let rewrite_template = F.asprintf "%a\n%s" AE.pp AE.mask_token matched_part in
      [Sed {rewrite_template; source_path; line}]


and apply_instruction instr =
  match instr with
  | Comby {match_template; rewrite_template; source_path; line} ->
      let open IResult.Let_syntax in
      let line_to_match = List.nth_exn (read_lines source_path) (line - 1) in
      let match_results = match_comby match_template source_path line line_to_match in
      let results =
        List.map match_results ~f:(fun mr ->
            let* matched = mr in
            let* replacement = replace ~matched ~rewrite_template ~line_to_match in
            let rewritten_source = replacement.Comby_kernel.Replacement.replacement_content in
            if String.is_substring rewritten_source ~substring:"!\"<FL4APR_MASK>\"" then
              Error "Redundant"
            else
              Ok
                { rewritten_source= replacement.Comby_kernel.Replacement.replacement_content
                ; matched_part= matched.Match.matched } )
      in
      results
  | Sed {rewrite_template; line; source_path} ->
      let matched_part = List.nth_exn (read_lines source_path) (line - 1) in
      [Ok {rewritten_source= rewrite_template; matched_part}]


and match_comby match_template source_path line line_to_match : (match', string) Result.t list =
  let open Matchers in
  let matching_context = {match_template; source_path; line} in
  match Hashtbl.find_opt comby_match_tbl matching_context with
  | Some matched ->
      matched
  | _ ->
      let result =
        let specification = Specification.create ~match_template () in
        let configuration =
          Configuration.create ~disable_substring_matching:true ~match_newline_toplevel:false ()
        in
        match
          Comby.Pipeline.execute ~metasyntax ~configuration java_matcher (String line_to_match)
            specification
        with
        | Matches (matches, n) when n > 0 ->
            List.map
              ~f:(fun m ->
                Result.Ok
                  (Result.ok_or_failwith (Comby_kernel.Match.to_yojson m |> Match.of_yojson)) )
              matches
        | _ ->
            [ Result.Error
                (F.asprintf "No match found for %a at line  %d" pp_matching_context matching_context
                   line ) ]
      in
      Hashtbl.add comby_match_tbl matching_context result ;
      result


and replace ~matched ~rewrite_template ~line_to_match :
    (Comby_kernel.Replacement.t, string) Result.t =
  let open Matchers in
  let Match.{range; environment} = matched in
  match Rewrite.all ~source:line_to_match ~metasyntax ~rewrite_template [matched] with
  | Some rep ->
      Replacement.{range; environment; replacement_content= rep.rewritten_source}
      |> Replacement.to_yojson |> Comby_kernel.Replacement.of_yojson
  | None ->
      Result.Error ("No replacement found for pattern" ^/ rewrite_template)


let apply =
  extract_rewrite_instructions
  >>> List.concat_map ~f:(fun instr ->
          List.map (apply_instruction instr) ~f:(fun result ->
              {cmd= instruction_to_string instr; result} ) )
