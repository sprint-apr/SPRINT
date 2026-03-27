open! IStd
open! Vocab

let pgm = lazy (Program.from_marshal ())

type package = string

type klass = Typ.Name.t

let get_classes_under_package package =
  List.filter
    ~f:(fun klass ->
      let pkg = klass |> Typ.Name.Java.get_java_class_name_exn >@ JavaClassName.package in
      String.equal pkg package && not (Program.Class.is_testclass klass) )
    (Program.all_classes !!pgm)


module type S = sig
  type component

  type on

  val collect : ?pred:(component -> bool) -> on -> component list
end

module Make (C : sig
  type component

  type on

  val name : string

  val compare_component : component -> component -> int

  val collect : on -> component list
end) : S with type component = C.component and type on = C.on = struct
  include C

  module CSet = Caml.Set.Make (struct
    type t = component [@@deriving compare]
  end)

  let cache : (on, component list) Cache.t = Cache.create ()

  let collect ?(pred = fun _ -> true) (on : on) =
    Profiler.start_event (name ^ ".collector") ;
    (let components =
       Cache.find_or_compute cache on ~compute:(fun () ->
           C.collect on |> CSet.of_list |> CSet.elements )
     in
     List.filter components ~f:pred )
    |> Profiler.finish_with_value (name ^ ".collector")
end

module Variables = Make (struct
  type component = Pvar.t * Typ.t [@@deriving compare]

  type on = Procname.t

  let name = "Variables"

  let collect mthd =
    let ProcAttributes.{proc_name; formals; locals} =
      Procdesc.get_attributes (Program.pdesc_of !!pgm mthd)
    in
    let local_name_and_types = List.map locals ~f:(fun ProcAttributes.{name; typ} -> (name, typ)) in
    let this_var =
      ( Mangled.from_string "this"
      , proc_name >@ Procname.get_class_type_name |> Typ.mk_struct |> Typ.mk_ptr )
    in
    List.filter_map
      ((this_var :: formals) @ local_name_and_types)
      ~f:(fun (name, typ) ->
        let pv = Pvar.mk name proc_name in
        Option.some_if (not (Pvar.is_frontend_tmp pv)) (pv, typ) )
end)

module Literals = Make (struct
  type component = Const.t [@@deriving compare]

  type on = package

  let name = "Literals"

  module ConstMap = Caml.Map.Make (struct
    type t = Const.t [@@deriving compare]
  end)

  module ConstSet = PrettyPrintable.MakePPSet (struct
    type t = Const.t [@@deriving compare]

    let pp = Const.pp Pp.text
  end)

  let extract_literals =
    IRUtils.fold_expr
      ~f:(fun acc e ->
        match (e : Exp.t) with Const ((Cint _ | Cstr _ | Cfloat _) as c) -> c :: acc | _ -> [] )
      ~init:[]


  let collect_from_node node =
    Instrs.fold (Procdesc.Node.get_instrs node) ~init:[] ~f:(fun acc instr ->
        Sil.exps_of_instr instr @ acc )
    |> List.concat_map ~f:extract_literals


  let collect package =
    let literal_counts : (Const.t * int) list =
      get_classes_under_package package
      |> List.fold ~init:[] ~f:(fun acc kls ->
             Procname.Set.elements (Program.methods_in_class !!pgm kls) @ acc )
      |> List.concat_map ~f:(fun procname -> Program.get_nodes !!pgm procname)
      |> List.concat_map ~f:(collect_from_node <<< InterNode.pnode_of)
      |> List.fold ~init:ConstMap.empty ~f:(fun acc const ->
             ConstMap.update const (function None -> Some 0 | Some cnt -> Some (Int.succ cnt)) acc )
      |> ConstMap.bindings
    in
    let ints, strings, floats =
      List.partition3_map literal_counts ~f:(fun ((lit, _) as pair) ->
          match[@warning "-8"] (lit : Const.t) with
          | Cint _ ->
              `Fst pair
          | Cstr _ ->
              `Snd pair
          | Cfloat _ ->
              `Trd pair )
    in
    List.fold
      ~f:(fun acc pairs ->
        let sorted : Const.t list =
          List.sort pairs ~compare:(fun (_, cnt1) (_, cnt2) -> Int.compare cnt2 cnt1)
          |> List.map ~f:fst
        in
        ConstSet.union acc
          (ConstSet.of_list (List.take sorted Config.sprint_synthesizer_max_literal_num)) )
      ~init:ConstSet.empty [ints; strings; floats]
    |> ConstSet.elements
end)

module Classes = Make (struct
  type component = Typ.Name.t [@@deriving compare]

  type on = package

  let name = "Classes"

  let filter = function
    | Typ.JavaClass jname ->
        Option.is_none (JavaClassName.get_outer_class_name jname)
        && not (List.mem Program.Class.test_classes ~equal:Typ.Name.equal (Typ.JavaClass jname))
    | _ ->
        false


  let collect package = get_classes_under_package package |> List.filter ~f:filter
end)

module Methods = Make (struct
  type component = Procname.Java.t [@@deriving compare]

  type on = klass

  let name = "Methods"

  let filter name =
    let excludes =
      Procname.
        [ is_java_access_method
        ; is_java_anonymous_inner_class_method
        ; is_java_autogen_method
        ; is_java_class_initializer ]
    in
    not (List.exists excludes ~f:(( |> ) name))


  (* TODO: see method-signature *)
  let collect klass =
    Program.find_methods_in_class ~find_library_methods:true !!pgm klass
    |> Procname.Set.filter filter |> Procname.Set.elements
    |> List.map ~f:(Procname.as_java_exn ~explanation:"")
end)

module Fields = Make (struct
  type component = Fieldname.t [@@deriving compare]

  type on = klass

  let name = "Fields"

  let collect klass =
    match Tenv.lookup (Program.tenv ()) klass with
    | None ->
        []
    | Some Struct.{fields; statics} ->
        List.map (fields @ statics) ~f:Tuple3.get1
        |> List.filter ~f:(not <<< Fieldname.is_java_synthetic)
end)

module AccessExpressions = Make (struct
  type component = ASTExp.t [@@deriving compare]

  type on = Procname.t

  let name = "AccessExpressions"

  let collect_interesting_expressions_on_node n =
    Procdesc.Node.get_instrs n
    |> Instrs.fold ~init:[] ~f:(fun acc instr -> Sil.exps_of_instr instr @ acc)
    |> List.filter ~f:(function
         | Exp.Lvar pv when Pvar.is_frontend_tmp pv ->
             true
         | Exp.Var _ ->
             true
         | _ ->
             false )


  let collect mthd =
    let pdesc = Program.pdesc_of !!pgm mthd in
    let nodes = Procdesc.get_nodes pdesc in
    List.concat_map nodes ~f:collect_interesting_expressions_on_node
    |> List.filter_map ~f:(ASTExp.from_IR_exp_opt pdesc)
    |> List.filter ~f:(fun ae -> not (String.contains (F.asprintf "%a" ASTExp.pp ae) '$'))
end)
