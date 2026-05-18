open Contexts

type observer = { on_event : eval_ctx -> Event.t -> unit }

let default : observer = { on_event = (fun _ _ -> ()) }

let current : observer ref = ref default

let suppression_depth : int ref = ref 0

let notify (ctx : eval_ctx) (ev : Event.t) : unit =
  if !suppression_depth > 0 then ()
  else !current.on_event ctx ev

let notify_lazy (ctx : eval_ctx) (mk : unit -> Event.t) : unit =
  if !suppression_depth > 0 then ()
  else if !current == default then ()
  else !current.on_event ctx (mk ())

let with_suppressed (_ctx : eval_ctx) (f : unit -> 'a) : 'a =
  incr suppression_depth;
  let restore () = decr suppression_depth in
  match f () with
  | r -> restore (); r
  | exception e -> restore (); raise e
