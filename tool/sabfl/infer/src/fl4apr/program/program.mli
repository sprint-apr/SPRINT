open! IStd
open! Vocab

module Node : module type of InterNode

module NSet : module type of PrettyPrintable.MakePPSet (Node)

module ParamField : module type of struct
  type t = int * Fieldname.t [@@deriving compare]

  let pp fmt (i, fn) = F.fprintf fmt "%d.%a" i Fieldname.pp fn
end

module ParamFields : module type of AbstractDomain.FiniteSet (ParamField)

module SideEffects : module type of WeakMap.Make (Procname) (ParamFields)

module type AbsConstS = sig
  type t = NonNull | Primitive of Const.t | NonConst [@@deriving compare, equal]

  val pp : Formatter.t -> t -> unit

  val is_nonnull : t -> bool

  val is_nonconst : t -> bool

  val join : t -> t -> t
end

module AbsConst : AbsConstS

type field_info =
  { typ: Typ.t
  ; annotations: Annot.Item.t
  ; access: PredSymb.access
  ; is_static: bool
  ; is_final: bool
  ; initialization: Exp.t Option.t
        (** NOTE: the initializer of a final primitive field is None. The field accesses are
            automatically translated into compile-time constants *) }

type t

val construct_cg : t -> t

val tenv : unit -> Tenv.t

val to_marshal : string -> t -> unit

val from_marshal : ?do_preanalysis:(Procdesc.t -> unit) -> ?init:bool -> unit -> t

val marshalled_path : string

val add_call_edge : t -> InstrNode.t -> Procname.t -> unit

val add_param_typs : t -> Procname.t -> Exp.t * Typ.Name.Set.t -> unit

val callers_of_instr_node : t -> InstrNode.t -> Procname.t list

val callees_of_instr_node : t -> InstrNode.t -> Procname.t list

val callers_of_proc : t -> Procname.t -> Procname.t list

val callees_of_proc : t -> Procname.t -> Procname.t list

val unique_callee_of_instr_node_opt : t -> InstrNode.t -> Procname.t option

val is_library_call : t -> InstrNode.t -> bool

val add_library_call : t -> InstrNode.t -> unit

val add_entry : t -> Procname.t -> unit

val set_entry : t -> Procname.t list -> unit

val get_entries : t -> Procname.t list

val is_entry : t -> Procname.t -> bool

val has_instr : f:(Sil.instr -> bool) -> Node.t -> bool

val pdesc_of : t -> Procname.t -> Procdesc.t

val pdesc_of_opt : t -> Procname.t -> Procdesc.t option

val store_callgraph_as_db : t -> unit

val all_procs : t -> Procname.Set.t

val all_nodes : t -> InterNode.t list

val all_instr_nodes : t -> InstrNode.t list

val cg_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> Procname.Set.t -> Procname.Set.t

val cfg_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val dom_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val pdom_reachables_of : ?forward:bool -> ?reflexive:bool -> t -> NSet.t -> NSet.t

val is_reachable : t -> Node.t -> Node.t -> bool

val is_undef_proc : t -> Procname.t -> bool

val dom : t -> Node.t -> Node.t -> bool

val pdom : t -> Node.t -> Node.t -> bool

val pred : t -> Node.t -> Node.t list

val succ : t -> Node.t -> Node.t list

val pred_instr_node : t -> InstrNode.t -> InstrNode.t list

val succ_instr_node : t -> InstrNode.t -> InstrNode.t list

val get_files : t -> SourceFile.t list

val get_nodes : t -> Procname.t -> Node.t list

val get_exit_node : t -> Procname.t -> Node.t

val get_entry_node : t -> Procname.t -> Node.t

val get_exit_instr_node : t -> Procname.t -> InstrNode.t

val get_entry_instr_node : t -> Procname.t -> InstrNode.t

val find_node_with_location : t -> Location.t -> Node.t list

val type_hierachy : t -> Typ.t -> Typ.t -> three_value

val is_consistent_type : Typ.t -> Typ.t -> bool

val has_annot : t -> string -> Procname.t -> bool

val print_callgraph : t -> string -> unit

val print_classhierachy : t -> string -> unit

val print_param_typs : t -> string -> unit

val slice_virtual_calls : t -> Procname.Set.t -> Procname.Set.t -> unit

val slice_procs_except : t -> Procname.Set.t -> unit

val resolve_method : Typ.Name.t -> Procname.t -> Procname.t option

val resolve_methods : Procname.t -> Typ.Name.Set.t -> Procname.t list

val is_sliced_method : t -> Procname.t -> bool

val methods_in_class : ?find_library_methods:bool -> t -> Typ.Name.t -> Procname.Set.t

val find_methods_in_class :
  ?find_library_methods:bool -> ?pred:(Procname.t -> bool) -> t -> Typ.Name.t -> Procname.Set.t

val reset_cg : t -> t

val executed_by_jvm : t -> Procname.t -> Procname.Set.t

val remove_cfg_if_no_cg : t -> t

val is_recursive : t -> Procname.t -> bool

val is_self_recursive : Procname.t -> bool

val node_for_junit_premethods :
     t
  -> ?pdesc_opt:Procdesc.t option
  -> clinits:Procname.Set.t
  -> Typ.Name.t
  -> Procname.t
  -> Procdesc.Node.t

val get_expected_exn_typ : t -> Procname.t -> Typ.t option

val get_failing_test_methods : t -> (Typ.name * Procname.t) list

val all_pvars_of : t -> Procname.t -> (Pvar.t * Typ.t) list

val is_float : Typ.t -> bool

val all_classes : t -> Typ.Name.t list

val get_field_typ_opt : Fieldname.t -> Typ.t option

val get_pvar_typ_opt : Pvar.t -> Typ.t option

val find_recursive : Procname.Set.t -> unit

val wto_cg : t -> Procname.Set.t -> Procname.t WeakTopologicalOrder.Partition.t

val collect_callback_fields : t -> Fieldname.t list

val callee_dispatch : base_class:Typ.Name.t -> is_exact:bool -> Procname.Java.t -> Procname.Set.t

val array_length_field : Fieldname.t

val get_fieldinfo : t -> Fieldname.t -> field_info

val find_overloaded_methods : t -> Procname.Java.t -> Procname.Java.t list

module Class : sig
  type klass = Typ.name

  val test_classes : klass list

  val is_testclass : klass -> bool

  val is_testclass_str : string -> bool

  val has_child : t -> klass -> bool

  val find_all_children : t -> reflexive:bool -> klass -> klass list

  val find_siblings : t -> klass -> klass list

  val find_impl : t -> klass -> klass list

  val lookup : t -> klass -> Struct.t option

  val is_enum : t -> klass -> bool

  val is_interface : t -> klass -> bool

  val is_abstract : t -> klass -> bool
end

val is_innerclass_field : Fieldname.t -> bool

module CFG : sig
  module G : module type of Graph.Imperative.Digraph.ConcreteBidirectional (Node)

  val print_to_dot : t -> Procname.t -> path:string -> unit

  val find_outer_block_node : t -> Node.t -> Node.t option
  (** Returns the nearest outer block node node that is reachable from the given node. Returns None
      if a node is in the outermost block *)

  val is_switch_location : Location.t -> bool
end

val find_equals_proc : Typ.t -> Procname.t option

val is_interface_or_abstract_class_typ : Typ.t -> bool

val is_nonnull_static_final_field : Fieldname.t -> bool

val is_primitive_type : Typ.t -> bool

val find_common_superclasses : Typ.Name.t -> Typ.Name.t -> Typ.Name.Set.t

val has_nontrivial_common_parent : Typ.Name.t -> Typ.Name.t -> bool

val has_recursive_field : Typ.Name.t -> bool

val set_side_effects : t -> SideEffects.t -> unit

val side_effects : t -> SideEffects.t

val set_return_values : t -> AbsConst.t Procname.Map.t -> unit

val return_values : t -> AbsConst.t Procname.Map.t

val is_nonnull_proc : t -> Procname.t -> bool

val is_constant_proc : t -> Procname.t -> bool

val has_syntactic_getter : Fieldname.t -> bool
