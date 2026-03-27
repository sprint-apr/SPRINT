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

type exec =
     Procname.t
  -> Context.t
  -> Procdesc.Node.t
  -> Sil.instr
  -> Loc.t * Typ.t
  -> (Exp.t * Typ.t) list
  -> t
  -> exec_work:(Procname.t * Context.t -> t -> t)
  -> t

let add_to_collection pid ctx ~col_exp ~value state =
  let this_locs = eval_locs pid ctx col_exp state in
  let this_field_locs = PowLoc.append_fields this_locs ~fn:mElementsField in
  weak_update_mem_locs this_field_locs value state


let add_to_new_collection ~loc ~value state =
  let this_field = Loc.append_field loc ~fn:mElementsField in
  weak_update_mem this_field value state


let get_from_collection pid ctx ~col_exp state =
  let this_locs = eval_locs pid ctx col_exp state in
  let this_field_locs = PowLoc.append_fields this_locs ~fn:mElementsField in
  Mem.find_mem_set this_field_locs state.mem


let implements interfaces typename =
  List.exists interfaces ~f:(fun interface ->
      PatternMatch.Java.implements interface (Program.tenv ()) (Typ.Name.name typename) )


module Class = struct
  let cast pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    (* let[@warning "-8"] [(this_exp, _); (Exp.Sizeof {typ= {desc= Tstruct name}}, _)] = arg_typs in *)
    let[@warning "-8"] [(arg_exp, _); _] = arg_typs in
    let value = eval pid ctx arg_exp state in
    {state with reg= Reg.weak_update ret_loc value state.reg}


  let cast2 pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    (* let[@warning "-8"] [(this_exp, _); (Exp.Sizeof {typ= {desc= Tstruct name}}, _)] = arg_typs in *)
    let[@warning "-8"] [_; (arg_exp, _)] = arg_typs in
    let value = eval pid ctx arg_exp state in
    {state with reg= Reg.weak_update ret_loc value state.reg}


  let newInstance _ ctx node instr (ret_loc, _) _ state ~exec_work:_ =
    (* instantiate concrete type by dynamic information *)
    let instr_node = InstrNode.of_pnode node instr in
    let instance_names =
      let classes_of_ctx = DynInfo.get_class_info (Contexts.singleton ctx) instr_node in
      if Typ.Name.Set.is_empty classes_of_ctx then
        DynInfo.get_class_info (DynInfo.all_ctxs ()) instr_node
      else classes_of_ctx
    in
    let value =
      Typ.Name.Set.fold
        (fun name acc ->
          match
            Val.default_of_typ ~is_exact:true ~ctx:(Context.empty_of ctx)
              (Typ.mk_struct (Fl4aprModels.Class.get_underlying_name name))
          with
          | Some v ->
              L.progress " - create newInstance by %a@." Typ.Name.pp name ;
              Val.join v acc
          | None ->
              acc )
        instance_names Val.bottom
    in
    {state with reg= Reg.weak_update ret_loc value state.reg}
end

let alloc _ ctx node instr (ret_loc, _) _ state ~typ ~exec_work:_ =
  let allocsite = make_allocsite (Context.empty_of ctx) node instr in
  state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite typ ;
  let value = Val.of_locs (PowLoc.singleton allocsite) in
  {state with reg= Reg.weak_update ret_loc value state.reg}


module Collection = struct
  let typ = Fl4aprModels.Collection.typ

  let add pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let value = eval pid ctx arg_exp state in
    add_to_collection pid ctx ~col_exp:this_exp ~value state


  let addAll pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let arg_value = get_from_collection pid ctx ~col_exp:arg_exp state in
    add_to_collection pid ctx ~col_exp:this_exp ~value:arg_value state


  let addAtIndex pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _ :: (arg_exp, _) :: _) = arg_typs in
    let value = eval pid ctx arg_exp state in
    add_to_collection pid ctx ~col_exp:this_exp ~value state


  let addAllAtIndex pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _ :: (arg_exp, _) :: _) = arg_typs in
    let arg_value = get_from_collection pid ctx ~col_exp:arg_exp state in
    add_to_collection pid ctx ~col_exp:this_exp ~value:arg_value state


  let iterator pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite Fl4aprModels.Collection.iterator_typ ;
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    { state with
      reg= Reg.weak_update ret_loc (allocsite |> PowLoc.singleton |> Val.of_locs) state.reg }
    |> add_to_new_collection ~loc:allocsite ~value:elements


  let next pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    {state with reg= Reg.weak_update ret_loc elements state.reg}


  let enumeration_of pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] [(this_exp, _)] = arg_typs in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite typ ;
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    let state = add_to_new_collection ~loc:allocsite ~value:elements state in
    {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) state.reg}


  let newCollectionFromArray pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] [(this_exp, _)] = arg_typs in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite typ ;
    let this_locs = eval_locs pid ctx this_exp state in
    let elements = Mem.find_mem_set (PowLoc.append_indexes this_locs) state.mem in
    let state = add_to_new_collection ~loc:allocsite ~value:elements state in
    {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) state.reg}


  let toArray pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <-
      Loc2Typ.add_typ state.loc2typ allocsite (Typ.mk_struct Typ.Name.Java.java_lang_object) ;
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    { state with
      reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) state.reg
    ; mem= Mem.weak_update (Loc.append_index allocsite) elements state.mem }


  let _of pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite typ ;
    let elements =
      List.fold arg_typs ~init:Val.bottom ~f:(fun acc (arg_exp, _) ->
          eval pid ctx arg_exp state |> Val.join acc )
    in
    let state = add_to_new_collection ~loc:allocsite ~value:elements state in
    {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) state.reg}


  let copyOf pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    let arg_exp, _ = List.hd_exn arg_typs in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite typ ;
    let elements = get_from_collection pid ctx ~col_exp:arg_exp state in
    let array_value =
      let this_locs = eval_locs pid ctx arg_exp state in
      let this_loc_indexs = PowLoc.append_indexes this_locs in
      Mem.find_mem_set this_loc_indexs state.mem
    in
    let state = add_to_new_collection ~loc:allocsite ~value:(Val.join elements array_value) state in
    {state with reg= Reg.weak_update ret_loc (Val.of_locs (PowLoc.singleton allocsite)) state.reg}


  let get pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    {state with reg= Reg.weak_update ret_loc elements state.reg}
end

module System = struct
  let arraycopy pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] [(src_exp, _); _; (dest_exp, _); _; _] = arg_typs in
    let src_locs = eval_locs pid ctx src_exp state |> PowLoc.append_indexes in
    let dest_locs = eval_locs pid ctx dest_exp state |> PowLoc.append_indexes in
    let elements = Mem.find_mem_set src_locs state.mem in
    weak_update_mem_locs dest_locs elements state
end

module EventListenerList = struct
  let add pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let value = eval pid ctx arg_exp state in
    add_to_collection pid ctx ~col_exp:this_exp ~value state


  let getListenerList pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let elements = get_from_collection pid ctx ~col_exp:this_exp state in
    let new_array = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <-
      Loc2Typ.add_typ state.loc2typ new_array (Typ.mk_array Typ.pointer_to_java_lang_object) ;
    let array_index_loc = Loc.append_index new_array in
    { state with
      reg= Reg.weak_update ret_loc (new_array |> PowLoc.singleton |> Val.of_locs) state.reg
    ; mem= Mem.weak_update array_index_loc elements state.mem }
end

module Concurrent = struct
  let get pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    let this_exp, _ = List.hd_exn arg_typs in
    let this_locs = eval_locs pid ctx this_exp state in
    let field_locs = PowLoc.append_fields this_locs ~fn:mConcurrentField in
    let value = Mem.find_mem_set field_locs state.mem in
    {state with reg= Reg.weak_update ret_loc value state.reg}


  let newPool _ ctx node instr (ret_loc, _) _ state ~exec_work:_ =
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite Fl4aprModels.Concurrent.pool_typ ;
    let value = Val.of_locs (PowLoc.singleton allocsite) in
    {state with reg= Reg.weak_update ret_loc value state.reg}


  let newThread2 pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: (arg_exp, _) :: _) = arg_typs in
    let this_field_locs =
      eval_locs pid ctx this_exp state |> PowLoc.append_fields ~fn:mRunnableField
    in
    let value = eval pid ctx arg_exp state in
    weak_update_mem_locs this_field_locs value state


  let newThread3 pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _ :: (arg_exp, _) :: _) = arg_typs in
    let this_field_locs =
      eval_locs pid ctx this_exp state |> PowLoc.append_fields ~fn:mRunnableField
    in
    let value = eval pid ctx arg_exp state in
    weak_update_mem_locs this_field_locs value state


  let dispatch state ~locs ~pname =
    let program = Program.from_marshal () in
    PowLoc.fold
      (fun loc acc ->
        try
          match type_of_loc state loc |> AbsTyp.typ_of |> Typ.name with
          | Some name -> (
            match Tenv.lookup (Program.tenv ()) name with
            | Some Struct.{methods} ->
                List.filter methods ~f:(String.equal pname <<< Procname.get_method)
                |> List.filter ~f:(not <<< Program.is_undef_proc program)
                |> Procname.Set.of_list |> Procname.Set.union acc
            | None ->
                acc )
          | None ->
              acc
        with Caml.Not_found -> acc )
      locs Procname.Set.empty


  let dispatch_callable pid ctx arg_typs state =
    let[@warning "-8"] [_; (callable_exp, _)] = arg_typs in
    let callable_locs = eval_locs pid ctx callable_exp state in
    dispatch state ~locs:callable_locs ~pname:"call"


  let dispatch_runnable pid ctx arg_typs state =
    let[@warning "-8"] [(this_exp, _)] = arg_typs in
    let this_locs = eval_locs pid ctx this_exp state in
    let runnable_val =
      Mem.find_mem_set (PowLoc.append_fields ~fn:mRunnableField this_locs) state.mem
    in
    dispatch state ~locs:(Val.get_locs runnable_val) ~pname:"run"


  let start pid ctx _ _ _ arg_typs state ~exec_work =
    (* thread.start();
       - runnable = thread.mRunnableField in
       - runnable.run();
    *)
    let program = Program.from_marshal () in
    let runnable_procs = dispatch_runnable pid ctx arg_typs state in
    if Procname.Set.is_empty runnable_procs |> not then
      L.progress " - find runnable methods: %a@." Procname.Set.pp runnable_procs
    else L.progress " - not found runnable methods: %a@." Procname.Set.pp runnable_procs ;
    let[@warning "-8"] [(this_exp, _)] = arg_typs in
    let field_locs = eval_locs pid ctx this_exp state |> PowLoc.append_fields ~fn:mRunnableField in
    let runnable_value = Mem.find_mem_set field_locs state.mem in
    Procname.Set.fold
      (fun callee state ->
        let this_pvar, _ =
          Procdesc.get_pvar_formals (Program.pdesc_of program callee) |> List.hd_exn
        in
        let state =
          {state with mem= Mem.weak_update (Loc.of_pvar this_pvar ~ctx) runnable_value state.mem}
        in
        exec_work (callee, ctx) state )
      runnable_procs state


  let submit pid ctx node instr (ret_loc, _) arg_typs state ~exec_work =
    (* ret_loc = executor.submit(callable_exp);
       - execute callable_exp.call()
       * ret_loc := future_value
       * future_value.concurrentField := m[callable_exp.call().return]
    *)
    let program = Program.from_marshal () in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite Fl4aprModels.Concurrent.future_typ ;
    let future_value = Val.of_locs (PowLoc.singleton allocsite) in
    let callable_procs = dispatch_callable pid ctx arg_typs state in
    if Procname.Set.is_empty callable_procs |> not then
      L.progress " - find callable methods: %a@." Procname.Set.pp callable_procs
    else L.progress " - not found callable methods: %a@." Procname.Set.pp callable_procs ;
    let[@warning "-8"] [_; (callable_exp, _)] = arg_typs in
    let this_actual = eval pid ctx callable_exp state in
    let value, state =
      Procname.Set.fold
        (fun callee (value_acc, state) ->
          let this_pvar, _ =
            Procdesc.get_pvar_formals (Program.pdesc_of program callee) |> List.hd_exn
          in
          let state =
            {state with mem= Mem.weak_update (Loc.of_pvar this_pvar ~ctx) this_actual state.mem}
          in
          let state = exec_work (callee, ctx) state in
          let callee_ret_var = Procdesc.get_ret_var (Program.pdesc_of program callee) in
          let ret_value = Mem.find (Loc.of_pvar ~ctx callee_ret_var) state.mem in
          (Val.join ret_value value_acc, state) )
        callable_procs (Val.bottom, state)
    in
    { state with
      reg= Reg.weak_update ret_loc future_value state.reg
    ; mem= Mem.weak_update (Loc.append_field allocsite ~fn:mConcurrentField) value state.mem }
end

module Map = struct
  let put pid ctx _ _ _ arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: (key_exp, _) :: (value_exp, _) :: _) = arg_typs in
    let this_locs = eval_locs pid ctx this_exp state in
    let key_value = eval pid ctx key_exp state in
    let value_value = eval pid ctx value_exp state in
    weak_update_mem_locs (PowLoc.append_fields this_locs ~fn:mKeysField) key_value state
    |> weak_update_mem_locs (PowLoc.append_fields this_locs ~fn:mValuesField) value_value


  let get pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_field_locs =
      eval_locs pid ctx this_exp state |> PowLoc.append_fields ~fn:mValuesField
    in
    let value = Mem.find_mem_set this_field_locs state.mem in
    {state with reg= Reg.weak_update ret_loc value state.reg}


  let values pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
    let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
    let this_field_locs =
      eval_locs pid ctx this_exp state |> PowLoc.append_fields ~fn:mValuesField
    in
    let value = Mem.find_mem_set this_field_locs state.mem in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite object_typ ;
    let state = add_to_new_collection ~loc:allocsite ~value state in
    {state with reg= Reg.weak_update ret_loc (PowLoc.singleton allocsite |> Val.of_locs) state.reg}


  let newEmpty _ ctx node instr (ret_loc, _) _ state ~exec_work:_ =
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite Fl4aprModels.MapBuilder.map_typ ;
    {state with reg= Reg.weak_update ret_loc (PowLoc.singleton allocsite |> Val.of_locs) state.reg}
end

module MapBuilder = struct
  let init pid ctx node instr _ arg_typs state ~exec_work:_ =
    (* this.map := allocsite *)
    let this_exp, _ = List.hd_exn arg_typs in
    let allocsite = make_allocsite (Context.empty_of ctx) node instr in
    state.loc2typ <- Loc2Typ.add_typ state.loc2typ allocsite Fl4aprModels.MapBuilder.map_typ ;
    let this_locs = eval_locs pid ctx this_exp state in
    let this_map_locs = PowLoc.append_fields this_locs ~fn:mMapField in
    weak_update_mem_locs this_map_locs (PowLoc.singleton allocsite |> Val.of_locs) state


  let put pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    (* this.map -> loc
     * loc.mKeys := loc.mKeys + key 
     * loc.mValues := loc.mValues + value
     * return := this
     *)
    let[@warning "-8"] ((this_exp, _) :: (key_exp, _) :: (value_exp, _) :: _) = arg_typs in
    let this_locs = eval_locs pid ctx this_exp state in
    let this_value = Val.of_locs this_locs in
    let map_locs =
      Mem.find_mem_set (PowLoc.append_fields this_locs ~fn:mMapField) state.mem |> Val.get_locs
    in
    let key_value = eval pid ctx key_exp state in
    let value_value = eval pid ctx value_exp state in
    let state = {state with reg= Reg.weak_update ret_loc this_value state.reg} in
    weak_update_mem_locs (PowLoc.append_fields map_locs ~fn:mKeysField) key_value state
    |> weak_update_mem_locs (PowLoc.append_fields map_locs ~fn:mValuesField) value_value


  let build pid ctx _ _ (ret_loc, _) arg_typs state ~exec_work:_ =
    (* return := this.map *)
    let this_exp, _ = List.hd_exn arg_typs in
    let this_locs = eval_locs pid ctx this_exp state in
    let value = Mem.find_mem_set (PowLoc.append_fields ~fn:mMapField this_locs) state.mem in
    {state with reg= Reg.weak_update ret_loc value state.reg}
end

let asList pid ctx node instr (ret_loc, _) arg_typs state ~exec_work:_ =
  let[@warning "-8"] ((this_exp, _) :: _) = arg_typs in
  let new_list = make_allocsite (Context.empty_of ctx) node instr in
  state.loc2typ <- Loc2Typ.add_typ state.loc2typ new_list object_typ ;
  let new_list_value = Val.of_locs (PowLoc.singleton new_list) in
  let array_value =
    let this_locs = eval_locs pid ctx this_exp state in
    let this_loc_indexs = PowLoc.append_indexes this_locs in
    Mem.find_mem_set this_loc_indexs state.mem
  in
  {state with reg= Reg.weak_update ret_loc new_list_value state.reg}
  |> add_to_new_collection ~loc:new_list ~value:array_value


let exec_unknown _ ctx _ _ (ret_loc, ret_typ) _ state ~exec_work:_ =
  match Val.default_of_typ ~is_exact:false ~ctx:(Context.empty_of ctx) ret_typ with
  | Some value ->
      let loc = Val.get_locs value |> PowLoc.choose in
      state.loc2typ <- Loc2Typ.add_typ state.loc2typ loc (Typ.strip_ptr ret_typ) ;
      {state with reg= Reg.weak_update ret_loc value state.reg}
  | None ->
      (* L.progress "could not find default value for %a at %a@." (Typ.pp_full Pp.text) ret_typ InstrNode.pp
         (InstrNode.of_pnode node instr) ; *)
      state


let _dispatch : Fl4aprModels.t -> exec = function
  | MBuiltIn Fl4aprModels.BuiltIn.Cast ->
      Class.cast
  | MClass Fl4aprModels.Class.Cast ->
      Class.cast2
  | MClass Fl4aprModels.Class.NewInstance ->
      Class.newInstance
  | MCollection Fl4aprModels.Collection.Add ->
      Collection.add
  | MCollection Fl4aprModels.Collection.AddAll | MCollection Fl4aprModels.Collection.InitFromCol ->
      Collection.addAll
  | MCollection Fl4aprModels.Collection.AddAtIndex ->
      Collection.addAtIndex
  | MCollection Fl4aprModels.Collection.AddAllAtIndex ->
      Collection.addAllAtIndex
  | MCollection Fl4aprModels.Collection.Enumeration
  | MCollection Fl4aprModels.Collection.NewCollectionFromCol ->
      Collection.enumeration_of
  | MCollection Fl4aprModels.Collection.NewCollectionFromArray ->
      Collection.newCollectionFromArray
  | MCollection Fl4aprModels.Collection.NewEmptyCollection
  | MCollection Fl4aprModels.Collection.EmptyEnumeration ->
      alloc ~typ:Collection.typ
  | MCollection Fl4aprModels.Collection.Iterator ->
      Collection.iterator
  | MCollection Fl4aprModels.Collection.Next ->
      Collection.next
  | MCollection Fl4aprModels.Collection.ToArray ->
      Collection.toArray
  | MCollection Fl4aprModels.Collection.Of ->
      Collection._of
  | MCollection Fl4aprModels.Collection.CopyOf ->
      Collection.copyOf
  | MCollection Fl4aprModels.Collection.Get ->
      Collection.get
  | MEventListenerList Fl4aprModels.EventListenerList.Add ->
      EventListenerList.add
  | MEventListenerList Fl4aprModels.EventListenerList.GetListenerList ->
      EventListenerList.getListenerList
  | MArrays Fl4aprModels.Arrays.AsList ->
      asList
  | MMap Fl4aprModels.Map.Get ->
      Map.get
  | MMap Fl4aprModels.Map.Put ->
      Map.put
  | MMap Fl4aprModels.Map.Values ->
      Map.values
  | MMap Fl4aprModels.Map.NewEmptyMap ->
      Map.newEmpty
  | MMapBuilder Fl4aprModels.MapBuilder.Init ->
      MapBuilder.init
  | MMapBuilder Fl4aprModels.MapBuilder.Put ->
      MapBuilder.put
  | MMapBuilder Fl4aprModels.MapBuilder.Build ->
      MapBuilder.build
  | MSystem Fl4aprModels.System.Arraycopy ->
      System.arraycopy
  | MConcurrent Fl4aprModels.Concurrent.Get ->
      Concurrent.get
  | MConcurrent Fl4aprModels.Concurrent.NewPool ->
      Concurrent.newPool
  | MConcurrent Fl4aprModels.Concurrent.NewThread2 ->
      Concurrent.newThread2
  | MConcurrent Fl4aprModels.Concurrent.NewThread3 ->
      Concurrent.newThread3
  | MConcurrent Fl4aprModels.Concurrent.Start ->
      Concurrent.start
  | MConcurrent Fl4aprModels.Concurrent.Submit ->
      Concurrent.submit
  | MBuiltIn Fl4aprModels.BuiltIn.InstanceOf
  | MBuiltIn Fl4aprModels.BuiltIn.UnwrapException
  | MBuiltIn Fl4aprModels.BuiltIn.GetArrayLength
  | MSystem Fl4aprModels.System.CurrentTimeMillis
  | MAssert _
  | MPreconditions _
  | MCollection Fl4aprModels.Collection.Contains
  | MCollection Fl4aprModels.Collection.HasNext
  | MCollection Fl4aprModels.Collection.IsEmpty
  | MCollection Fl4aprModels.Collection.Init
  | MCollection Fl4aprModels.Collection.Remove
  | MEventListenerList Fl4aprModels.EventListenerList.Init
  | MMap Fl4aprModels.Map.Remove
  | MMap Fl4aprModels.Map.Init
  | MEnum Fl4aprModels.Enum.Ordinal
  | MLang _
  | MObject _
  | MWriter _ 
  | MPrintWriter _ -> (* PrintWriter generate alias, but not important *)
      exec_unknown


let dispatch callee arg_typs =
  match Fl4aprModels.dispatch callee arg_typs with
  | Some model ->
      Some (_dispatch model)
  | None ->
      None
