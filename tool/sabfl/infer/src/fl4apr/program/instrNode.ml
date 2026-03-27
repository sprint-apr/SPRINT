open! IStd
open! Vocab
module F = Format
module L = Logging
module Hashtbl = Caml.Hashtbl

module InstrNode = struct
  type t = {inode: InterNode.t; instr: Sil.instr} [@@deriving compare]

  let compare x y =
    if InterNode.equal x.inode y.inode then Sil.compare_instr x.instr y.instr
    else InterNode.compare x.inode y.inode


  let equal = [%compare.equal: t]

  let equal_except_vflag x y =
    InterNode.equal x.inode y.inode && equal_instr_except_vflag x.instr y.instr


  let make inode instr = {inode; instr}

  let of_pnode pnode instr =
    let inode = InterNode.of_pnode pnode in
    {inode; instr}


  let dummy =
    {inode= InterNode.dummy (Procname.from_string_c_fun "FL4APR_DUMMY"); instr= Sil.skip_instr}


  let default = dummy

  let dummy_entry =
    {inode= InterNode.dummy (Procname.from_string_c_fun "FL4APR_entry"); instr= Sil.skip_instr}


  let dummy_exit =
    {inode= InterNode.dummy (Procname.from_string_c_fun "FL4APR_exit"); instr= Sil.skip_instr}


  let dummy_of str = {dummy with inode= InterNode.dummy (Procname.from_string_c_fun str)}

  let dummy_of_proc proc = {inode= InterNode.dummy proc; instr= Sil.skip_instr}

  let dummy_of_instr instr = {dummy with instr}

  let inode_of {inode} = inode

  let get_proc_name {inode} = InterNode.get_proc_name inode

  let get_instr {instr} = instr

  let get_instrs {instr} = Instrs.singleton instr

  let get_loc {inode} = InterNode.get_loc inode

  let list_of_pnode pnode =
    let inode = InterNode.of_pnode pnode in
    let instr_list = get_instrs_list pnode in
    List.map instr_list ~f:(fun instr -> {inode; instr})


  let pp fmt {inode; instr} =
    F.fprintf fmt "<%a, %a, %a>" InterNode.pp inode
      (Sil.pp_instr ~print_types:true Pp.text)
      instr SourceFile.pp (InterNode.get_loc inode).Location.file


  let pp_pretty fmt {inode; instr} =
    let pnode = InterNode.pnode_of inode in
    let loc = InterNode.get_loc inode in
    let instr_str =
      F.asprintf "%a" (Sil.pp_instr ~print_types:false Pp.text) instr |> String.length
    in
    if Location.equal Location.dummy loc then
      match InterNode.get_proc_name inode with
      | Procname.Java mthd when Procname.Java.is_constructor mthd ->
          F.fprintf fmt "%s(%d)" (Procname.Java.get_simple_class_name mthd) instr_str
      | proc_name ->
          F.fprintf fmt "%s(%d)" (Procname.get_method proc_name) instr_str
    else
      match instr with
      | Sil.Call (_, Const (Cfun procname), [(Exp.Sizeof _, _)], _, _) when is_new procname ->
          F.fprintf fmt "%a" Location.pp_file_pos loc
      | _ ->
          F.fprintf fmt "%a(%a,%d)" Location.pp_line loc Procdesc.Node.pp pnode instr_str


  let pp_id fmt {inode; instr} =
    let proc, pnode = inode in
    let instr_str =
      F.asprintf "%a" (Sil.pp_instr ~print_types:false Pp.text) instr |> String.length
    in
    F.fprintf fmt "%s_%a_%d" (Procname.to_filename proc) Procdesc.Node.pp pnode instr_str


  let vertex_name {inode; instr} =
    F.asprintf "\"%s-%a\"" (InterNode.to_string inode)
      (Sil.pp_instr ~print_types:true Pp.text)
      instr


  let is_first_instr {inode; instr} =
    let instrs = InterNode.get_instrs inode in
    if Instrs.is_empty instrs then true else Sil.equal_instr instr (Instrs.nth_exn instrs 0)


  let is_last_instr {inode; instr} =
    let instrs = InterNode.get_instrs inode in
    if Instrs.is_empty instrs then true
    else Sil.equal_instr instr (Option.value_exn (Instrs.last instrs))


  let is_intermediate ({instr} as node) =
    match instr with
    | (Load {e= Lvar pv} | Store {e1= Lvar pv}) when Pvar.is_frontend_tmp pv ->
        true
    | _ ->
        not (is_first_instr node)


  let is_call_node {instr} = is_call_instr instr

  let is_entry {inode} = InterNode.is_entry inode

  let is_junit_node {inode} = InterNode.is_junit_node inode

  let is_exit {inode} = InterNode.is_exit inode

  let get_first_from pnode =
    let instrs = Procdesc.Node.get_instrs pnode in
    if Instrs.nth_exists instrs 0 then of_pnode pnode (Instrs.nth_exn instrs 0)
    else of_pnode pnode Sil.skip_instr


  let get_last_from pnode =
    let instrs = Procdesc.Node.get_instrs pnode in
    match Instrs.last instrs with
    | Some instr ->
        of_pnode pnode instr
    | None ->
        of_pnode pnode Sil.skip_instr


  let pnode_of {inode} = InterNode.pnode_of inode

  let get_preds (n : t) =
    let pnode = pnode_of n in
    let instrs = get_instrs_list pnode in
    if is_first_instr n then List.map (Procdesc.Node.get_preds pnode) ~f:get_last_from
    else
      match List.findi instrs ~f:(fun _ instr' -> Sil.equal_instr n.instr instr') with
      | Some (idx, _) ->
          let instr = List.nth_exn instrs (idx - 1) in
          let inode = n.inode in
          [{inode; instr}]
      | None ->
          L.(die InternalError)
            "No next of %a@. - Intrs: %a@." pp n
            (Pp.seq (Sil.pp_instr ~print_types:false Pp.text))
            instrs


  let get_succs (n : t) =
    let pnode = pnode_of n in
    let instrs = get_instrs_list pnode in
    if is_last_instr n then List.map (Procdesc.Node.get_succs pnode) ~f:get_first_from
    else
      match List.findi instrs ~f:(fun _ instr' -> Sil.equal_instr n.instr instr') with
      | Some (idx, _) ->
          let instr = List.nth_exn instrs (idx + 1) in
          let inode = n.inode in
          [{inode; instr}]
      | None ->
          L.(die InternalError)
            "No next of %a@. - Intrs: %a@." pp n
            (Pp.seq (Sil.pp_instr ~print_types:false Pp.text))
            instrs


  let get_exn (n : t) =
    let exn_pnodes = Procdesc.Node.get_exn (InterNode.pnode_of n.inode) in
    List.map exn_pnodes ~f:get_first_from


  let get_kind {inode} = InterNode.get_kind inode

  let hash x = Hashtbl.hash (vertex_name x)

  let is_retnode n = is_return_instr n.instr
end

include InstrNode
module Map = PrettyPrintable.MakePPMap (InstrNode)
module Set = PrettyPrintable.MakePPSet (InstrNode)
module ASet = AbstractDomain.FiniteSet (InstrNode)
