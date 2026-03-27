open! IStd
open! Vocab
include Caml.Hashtbl

let create () = Caml.Hashtbl.create 1214

let find_or_compute cache key ~compute =
  Profiler.start_event "find_or_compute" ;
  ( match Profiler.pick "Cache finding" (fun () -> find_opt cache key) () with
  | Some cached ->
      Profiler.pick "Cache hit" (fun () -> cached) ()
  | None ->
      let value = compute () in
      add cache key value ;
      value )
  |> Profiler.finish_with_value "find_or_compute"
