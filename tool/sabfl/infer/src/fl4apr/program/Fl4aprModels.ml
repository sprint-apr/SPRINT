open! IStd
open! Vocab
module L = Logging
module F = Format

let implements_interfaces interfaces typename =
  List.exists interfaces ~f:(fun interface ->
      PatternMatch.Java.implements interface (Program.tenv ()) (Typ.Name.name typename) )


let is_collection_arg arg_typ =
  match strip_ptr arg_typ with
  | Typ.{desc= Tstruct name} ->
      implements_interfaces collection_classes name
  | _ ->
      false


let is_array_arg arg_typ = match strip_ptr arg_typ with Typ.{desc= Tarray _} -> true | _ -> false

let is_comparator_arg arg_typ =
  match strip_ptr arg_typ with
  | Typ.{desc= Tstruct name} ->
      implements_interfaces ["java.util.Comparator"] name
  | _ ->
      false


let is_int_arg = Typ.is_int

module BuiltIn = struct
  type models = InstanceOf | Cast | UnwrapException | GetArrayLength
end

module Enum = struct
  type models = Ordinal

  let classes = ["java.lang.Enum"]

  let implements = implements_interfaces classes
end

module Object = struct
  type models = HashCode

  let classes = ["java.lang.Object"]

  let implements = implements_interfaces classes
end

module Collection = struct
  type models =
    | Enumeration
    | EmptyEnumeration
    | NewEmptyCollection
    | NewCollectionFromCol
    | NewCollectionFromArray
    | Of
    | CopyOf
    | Init
    | InitFromCol
    | IsEmpty
    | Iterator
    | HasNext
    | Add
    | AddAll
    | AddAtIndex
    | AddAllAtIndex
    | Next
    | Contains
    | ToArray
    | Remove
    | Get

  let typ = Typ.Name.Java.from_string "java.util.Collection" |> Typ.mk_struct

  let iterator_typ = Typ.Name.Java.from_string "java.util.Iterator" |> Typ.mk_struct

  let implements = implements_interfaces collection_classes
end

module System = struct
  type models = CurrentTimeMillis | Arraycopy

  let implements = implements_interfaces ["java.lang.System"]
end

module Class = struct
  type models = Cast | NewInstance

  let classes = ["java.lang.Class"]

  let from_underlying_string class_str =
    let underlying_name = java_class_from_string class_str in
    let underlying_typ = Typ.mk_struct underlying_name in
    Typ.Name.Cpp.from_qual_name
      (Typ.Template {mangled= None; args= [TType underlying_typ]})
      (QualifiedCppName.of_qual_string "java.lang.Class")


  let get_underlying_name : Typ.Name.t -> Typ.Name.t = function
    | JavaClass _ ->
        Typ.Name.Java.java_lang_object
    | CppClass (_, Template {args= [TType Typ.{desc= Tstruct underlying_name}]}) ->
        underlying_name
    | _ as name ->
        L.(die InternalError) "Invalid name type : %a" Typ.Name.pp name


  let implements : Typ.Name.t -> bool = function
    | JavaClass _ as name ->
        implements_interfaces classes name
    | CppClass (cpp_name, _) ->
        String.equal "java.lang.Class" (QualifiedCppName.to_qual_string cpp_name)
    | _ ->
        false
end

module Lang = struct
  type models =
    | Init
    | InitDefault
    | InitSize
    | Format
    | IsEmpty
    | Length
    | Append
    | ToString
    | Contains

  let classes = ["java.lang.String"; "java.lang.StringBuilder"; "java.lang.StringBuffer"]

  let implements = implements_interfaces classes
end

module Writer = struct
  type models = Init | Append | Write | ToString

  let field = Fieldname.make (Typ.Name.Java.from_string "java.io.Writer") "buf"

  let classes = ["java.io.Writer"]

  let typ = Typ.mk_struct (Typ.Name.Java.from_string "java.io.Writer")

  let implements = implements_interfaces classes
end

module PrintWriter = struct
  type models = InitArg | InitNew | Append | Write | ToString | Println

  let field = Fieldname.make (Typ.Name.Java.from_string "java.io.PrintWriter") "out"

  let classes = ["java.io.PrintWriter"]

  let implements = implements_interfaces classes

  let is_writer_arg typ =
    match strip_ptr typ with Typ.{desc= Tstruct name} -> Writer.implements name | _ -> false
end

module Assert = struct
  type models = AssertSame | AssertEqualsConst | AssertEquals | Fail

  let implements name =
    let class_name = Typ.Name.name name in
    String.is_substring class_name ~substring:"Assert"
    || String.is_substring class_name ~substring:"TestCase"
end

module EventListenerList = struct
  type models = Init | Add | GetListenerList

  let classes = ["javax.swing.event.EventListenerList"]
end

module Arrays = struct
  type models = AsList

  let classes = ["java.util.Arrays"]
end

module Concurrent = struct
  type models = NewPool | Submit | Get | NewThread2 | NewThread3 | Start

  let pool_typ = Typ.mk_struct (Typ.Name.Java.from_string "java.util.concurrent.ExecutorService")

  let future_typ = Typ.mk_struct (Typ.Name.Java.from_string "java.util.concurrent.Future")

  let runnable_typ = Typ.mk_struct (Typ.Name.Java.from_string "java.lang.Runnable")

  let callable_typ = Typ.mk_struct (Typ.Name.Java.from_string "java.util.concurrent.Callable")

  let implements name =
    match String.rsplit2 ~on:'.' (Typ.Name.name name) with
    | Some ("java.util.concurrent", _) ->
        true
    | Some ("java.lang", "Thread") ->
        true
    | _ ->
        false


  let is_callable_typ arg_typ =
    match strip_ptr arg_typ with
    | Typ.{desc= Tstruct name} ->
        implements_interfaces ["java.util.concurrent.Callable"] name
    | _ ->
        false


  let is_runnable_typ arg_typ =
    match strip_ptr arg_typ with
    | Typ.{desc= Tstruct name} ->
        implements_interfaces ["java.lang.Runnable"] name
    | _ ->
        false
end

module Map = struct
  type models = Get | Put | Remove | Values | Init | NewEmptyMap

  let typ = Typ.mk_struct (Typ.Name.Java.from_string "java.util.Map")

  let implements = implements_interfaces ["java.util.Map"; "com.google.common.collect.Maps"]
end

module MapBuilder = struct
  type models = Init | Build | Put

  let map_typ = Typ.mk_struct (Typ.Name.Java.from_string "java.util.Map")

  let implements = implements_interfaces ["com.google.common.collect.ImmutableMap$Builder"]
end

module Preconditions = struct
  type models = CheckState | CheckNotNull

  let implements = implements_interfaces ["com.google.common.base.Preconditions"]
end

type t =
  | MBuiltIn of BuiltIn.models
  | MEnum of Enum.models
  | MClass of Class.models
  | MCollection of Collection.models
  | MSystem of System.models
  | MLang of Lang.models
  | MWriter of Writer.models
  | MPrintWriter of PrintWriter.models
  | MAssert of Assert.models
  | MEventListenerList of EventListenerList.models
  | MArrays of Arrays.models
  | MConcurrent of Concurrent.models
  | MMap of Map.models
  | MMapBuilder of MapBuilder.models
  | MPreconditions of Preconditions.models
  | MObject of Object.models

let dispatch callee arg_typs : t option =
  let callee_name = Procname.get_method callee in
  match Procname.get_class_type_name callee with
  | _ when Procname.equal BuiltinDecl.__instanceof callee ->
      Some (MBuiltIn BuiltIn.InstanceOf)
  | _ when Procname.equal BuiltinDecl.__cast callee ->
      Some (MBuiltIn BuiltIn.Cast)
  | _ when Procname.equal BuiltinDecl.__unwrap_exception callee ->
      Some (MBuiltIn BuiltIn.UnwrapException)
  | _ when Procname.equal BuiltinDecl.__get_array_length callee ->
      Some (MBuiltIn BuiltIn.GetArrayLength)
  | Some name when Enum.implements name -> (
    match arg_typs with
    | _ when String.equal callee_name "ordinal" ->
        Some (MEnum Enum.Ordinal)
    | _ ->
        None )
  | Some name when Class.implements name -> (
    match arg_typs with
    | [_; _] when String.equal callee_name "cast" ->
        Some (MClass Class.Cast)
    | [_] when String.equal callee_name "newInstance" ->
        Some (MClass Class.NewInstance)
    | _ ->
        None )
  | Some name when implements_interfaces collection_classes name -> (
    match arg_typs with
    | _ when String.equal "enumeration" callee_name ->
        Some (MCollection Collection.Enumeration)
    | _
      when List.mem
             ["emptyEnumeration"; "emptySet"; "emptyList"; "emptyMap"]
             ~equal:String.equal callee_name ->
        Some (MCollection Collection.EmptyEnumeration)
    | [] when String.is_prefix callee_name ~prefix:"new" ->
        Some (MCollection Collection.NewEmptyCollection)
    | [arg_typ] when String.is_prefix callee_name ~prefix:"new" ->
        if is_collection_arg arg_typ then Some (MCollection Collection.NewCollectionFromCol)
        else if is_array_arg arg_typ then Some (MCollection Collection.NewCollectionFromArray)
        else if is_comparator_arg arg_typ || is_int_arg arg_typ then
          Some (MCollection Collection.NewEmptyCollection)
        else None
    | [_] when Procname.is_constructor callee ->
        Some (MCollection Collection.Init)
    | [_; arg_typ] when Procname.is_constructor callee ->
        if is_int_arg arg_typ || is_comparator_arg arg_typ then Some (MCollection Collection.Init)
        else if is_collection_arg arg_typ then Some (MCollection Collection.InitFromCol)
        else None
    | _ when String.equal "isEmpty" callee_name ->
        Some (MCollection Collection.IsEmpty)
    | _ when List.mem ["iterator"; "descendingIterator"] ~equal:String.equal callee_name ->
        Some (MCollection Collection.Iterator)
    | _ when String.equal "hasNext" callee_name ->
        Some (MCollection Collection.HasNext)
    | [_; _] when List.mem ["add"; "push"] ~equal:String.equal callee_name ->
        Some (MCollection Collection.Add)
    | [_; arg_typ; _]
      when List.mem ["add"; "push"] ~equal:String.equal callee_name && is_int_arg arg_typ ->
        Some (MCollection Collection.AddAtIndex)
    | [_; _] when String.equal "addAll" callee_name ->
        Some (MCollection Collection.AddAll)
    | [_; arg_typ; _] when String.equal "addAll" callee_name && is_int_arg arg_typ ->
        Some (MCollection Collection.AddAllAtIndex)
    | _ when List.mem ["next"; "pop"] ~equal:String.equal callee_name ->
        Some (MCollection Collection.Next)
    | _ when String.equal "contains" callee_name ->
        Some (MCollection Collection.Contains)
    | _ when String.equal "toArray" callee_name ->
        Some (MCollection Collection.ToArray)
    | _ when String.equal "of" callee_name ->
        Some (MCollection Collection.Of)
    | _ when String.equal "copyOf" callee_name ->
        Some (MCollection Collection.CopyOf)
    | _ when String.equal "remove" callee_name ->
        Some (MCollection Collection.Remove)
    | [_; arg_typ] when String.equal "get" callee_name && is_int_arg arg_typ ->
        Some (MCollection Collection.Get)
    | [_] when String.equal "peek" callee_name ->
        Some (MCollection Collection.Get)
    | _ ->
        None )
  | Some name when Map.implements name -> (
    match arg_typs with
    | [_] when Procname.is_constructor callee ->
        Some (MMap Map.Init)
    | [] when String.is_prefix ~prefix:"new" callee_name ->
        Some (MMap Map.NewEmptyMap)
    | _ when String.equal "get" callee_name ->
        Some (MMap Map.Get)
    | _ when String.equal "put" callee_name ->
        Some (MMap Map.Put)
    | _ when String.equal "values" callee_name ->
        Some (MMap Map.Values)
    | _ when String.equal "remove" callee_name ->
        Some (MMap Map.Remove)
    | _ ->
        None )
  | Some name when MapBuilder.implements name -> (
    match arg_typs with
    | _ when Procname.is_constructor callee ->
        Some (MMapBuilder MapBuilder.Init)
    | [_; _; _] when String.equal "put" callee_name ->
        Some (MMapBuilder MapBuilder.Put)
    | _ when String.equal "build" callee_name ->
        Some (MMapBuilder MapBuilder.Build)
    | _ ->
        None )
  | Some name when System.implements name -> (
    match arg_typs with
    | _ when String.equal "currentTimeMillis" callee_name ->
        Some (MSystem System.CurrentTimeMillis)
    | _ when String.equal "arraycopy" callee_name ->
        Some (MSystem System.Arraycopy)
    | _ ->
        None )
  | Some name when implements_interfaces Lang.classes name -> (
    match arg_typs with
    | [_] when Procname.is_constructor callee ->
        Some (MLang Lang.InitDefault)
    | [_; arg_typ] when Procname.is_constructor callee && Typ.is_int arg_typ ->
        Some (MLang Lang.InitSize)
    | ([_; _] | [_; _; _]) when Procname.is_constructor callee ->
        Some (MLang Lang.Init)
    | _ when String.equal "format" callee_name ->
        Some (MLang Lang.Format)
    | _ when String.equal "isEmpty" callee_name ->
        Some (MLang Lang.IsEmpty)
    | _ when String.equal "length" callee_name ->
        Some (MLang Lang.Length)
    | _ when String.equal "append" callee_name ->
        Some (MLang Lang.Append)
    | _ when String.equal "toString" callee_name ->
        Some (MLang Lang.ToString)
    | _ when String.equal "contains" callee_name ->
        Some (MLang Lang.Contains)
    | _ ->
        None )
  | Some name when PrintWriter.implements name -> (
    match arg_typs with
    | _ :: arg_typ :: _ when Procname.is_constructor callee && PrintWriter.is_writer_arg arg_typ ->
        Some (MPrintWriter PrintWriter.InitArg)
    | _ when Procname.is_constructor callee ->
        Some (MPrintWriter PrintWriter.InitNew)
    | _ when String.equal "append" callee_name ->
        Some (MPrintWriter PrintWriter.Append)
    | _ when String.equal "write" callee_name ->
        Some (MPrintWriter PrintWriter.Write)
    | _ when String.equal "toString" callee_name ->
        Some (MPrintWriter PrintWriter.ToString)
    | _ when String.equal "println" callee_name ->
        Some (MPrintWriter PrintWriter.Println)
    | _ ->
        None )
  | Some name when Writer.implements name -> (
    match arg_typs with
    | _ when Procname.is_constructor callee ->
        Some (MWriter Writer.Init)
    | _ when String.equal "append" callee_name ->
        Some (MWriter Writer.Append)
    | _ when String.equal "write" callee_name ->
        Some (MWriter Writer.Write)
    | _ when String.equal "toString" callee_name ->
        Some (MWriter Writer.ToString)
    | _ ->
        None )
  | Some name when Assert.implements name -> (
    match arg_typs with
    | [_; _] when List.mem ["assertSame"; "assertNotSame"] ~equal:String.equal callee_name ->
        Some (MAssert Assert.AssertSame)
    | [msg_typ; _; _]
      when is_string_typ msg_typ
           && List.mem ["assertSame"; "assertNotSame"] ~equal:String.equal callee_name ->
        Some (MAssert Assert.AssertSame)
    | [_]
      when List.mem
             ["assertTrue"; "assertFalse"; "assertNull"; "assertNotNull"]
             ~equal:String.equal callee_name ->
        Some (MAssert Assert.AssertEqualsConst)
    | [msg_typ; _]
      when is_string_typ msg_typ
           && List.mem
                ["assertTrue"; "assertFalse"; "assertNull"; "assertNotNull"]
                ~equal:String.equal callee_name ->
        Some (MAssert Assert.AssertEqualsConst)
    | _ when List.mem ["assertEquals"; "assertTypeEquals"] ~equal:String.equal callee_name ->
        Some (MAssert Assert.AssertEquals)
    | _ when String.equal "fail" callee_name ->
        Some (MAssert Assert.Fail)
    | _ ->
        None )
  | Some name when implements_interfaces EventListenerList.classes name -> (
    match arg_typs with
    | _ when Procname.is_constructor callee ->
        Some (MEventListenerList EventListenerList.Init)
    | _ when String.equal "add" callee_name ->
        Some (MEventListenerList EventListenerList.Add)
    | _ when List.mem ["getListenerList"; "getListeners"] ~equal:String.equal callee_name ->
        Some (MEventListenerList EventListenerList.GetListenerList)
    | _ ->
        None )
  | Some name when implements_interfaces Arrays.classes name -> (
    match arg_typs with
    | [_] when String.equal "asList" callee_name ->
        Some (MArrays Arrays.AsList)
    | _ ->
        None )
  | Some name when Concurrent.implements name -> (
    match arg_typs with
    | _ :: arg_typ :: _ when Procname.is_constructor callee && Concurrent.is_runnable_typ arg_typ ->
        Some (MConcurrent Concurrent.NewThread2)
    | _ :: _ :: arg_typ :: _
      when Procname.is_constructor callee && Concurrent.is_runnable_typ arg_typ ->
        Some (MConcurrent Concurrent.NewThread3)
    | _ when String.equal "newCachedThreadPool" callee_name ->
        Some (MConcurrent Concurrent.NewPool)
    | [_; arg_typ] when String.equal "submit" callee_name && Concurrent.is_callable_typ arg_typ ->
        Some (MConcurrent Concurrent.Submit)
    | _ when String.equal "get" callee_name ->
        Some (MConcurrent Concurrent.Get)
    | [_] when List.mem ["start"; "run"] ~equal:String.equal callee_name ->
        Some (MConcurrent Concurrent.Start)
    | _ ->
        None )
  | Some name when Preconditions.implements name -> (
    match arg_typs with
    | _ when String.equal "checkState" callee_name ->
        Some (MPreconditions Preconditions.CheckState)
    | _ when String.equal "checkNotNull" callee_name ->
        Some (MPreconditions Preconditions.CheckNotNull)
    | _ ->
        None )
  | Some name when Object.implements name -> (
    match arg_typs with
    | [_] when String.equal "hashCode" callee_name ->
        Some (MObject Object.HashCode)
    | _ ->
        None )
  | _ ->
      None
