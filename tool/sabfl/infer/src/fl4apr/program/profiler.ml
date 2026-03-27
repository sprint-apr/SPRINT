open! IStd
open! Vocab
module F = Format
module L = Logging
module StringMap = PrettyPrintable.MakePPMap (String)
module Hashtbl = Caml.Hashtbl

type t = (string, stat) Hashtbl.t

and stat = {mutable count: int; mutable stack: int; mutable time: float; mutable acc_time: float}

let prof : t = Hashtbl.create 1214

let start_event event =
  let st = Unix.gettimeofday () in
  match Hashtbl.find_opt prof event with
  | Some stat ->
      stat.time <- (if stat.stack > 0 then stat.time else st) ;
      stat.count <- stat.count + 1 ;
      stat.stack <- stat.stack + 1
  | None ->
      Hashtbl.add prof event {count= 1; stack= 1; time= st; acc_time= 0.0}


let finish_event event =
  let ft = Unix.gettimeofday () in
  match Hashtbl.find_opt prof event with
  | Some stat ->
      stat.stack <- stat.stack - 1 ;
      if Int.equal stat.stack 0 then (
        stat.time <- ft -. stat.time ;
        stat.acc_time <- stat.acc_time +. stat.time )
  | None ->
      L.die InternalError "Profiler: finishing event %s which have never been started" event


let finish_with_value event e =
  finish_event event ;
  e


let pp fmt prof =
  let tot_time = Hashtbl.fold (fun _ {acc_time} acc -> acc +. acc_time) prof 0.0 in
  let print entries =
    List.iter
      ~f:(fun (ev, {count; stack; acc_time}) ->
        assert (Int.equal stack 0) ;
        let percentage = acc_time /. tot_time *. 100.0 in
        F.fprintf fmt "%30s   -->  %10d times, %5.3f sec. (%2.1f%%)@." ev count acc_time percentage
        )
      entries
  in
  let entries = Hashtbl.fold (fun ev stat acc -> (ev, stat) :: acc) prof [] in
  let sorted_by_time =
    List.sort ~compare:(fun (_, {acc_time= x}) (_, {acc_time= y}) -> Float.compare y x) entries
  in
  let sorted_by_count =
    List.sort ~compare:(fun (_, {count= x}) (_, {count= y}) -> Int.compare y x) entries
  in
  F.fprintf fmt "=============== SORTED BY TIME ELAPSED =================\n" ;
  print sorted_by_time ;
  F.fprintf fmt "\n\n\n" ;
  F.fprintf fmt "=============== SORTED BY NUM CALLS =================\n" ;
  print sorted_by_count


let pick (event : string) (f : 'a -> 'b) (arg : 'a) : 'b =
  start_event event ;
  let value = f arg in
  finish_event event ;
  value


let report ?(path = Config.results_dir ^/ "profile") () =
  Utils.with_file_out path ~f:(fun oc -> F.fprintf (F.formatter_of_out_channel oc) "%a@." pp prof)
