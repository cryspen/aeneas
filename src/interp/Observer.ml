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

let with_suppressed (ctx : eval_ctx) (f : unit -> 'a) : 'a =
  incr suppression_depth;
  (* Mirror the suppression into [ctx.cert_events_suppressed] so the
     not-yet-migrated emit sites (which still go through
     [ctx_emit_event]) honor it. Removed in commit #10 once
     [cert_events_suppressed] leaves [eval_ctx]. -*)
  let prev_ctx_suppressed = !(ctx.cert_events_suppressed) in
  ctx.cert_events_suppressed := true;
  let restore () =
    decr suppression_depth;
    ctx.cert_events_suppressed := prev_ctx_suppressed
  in
  match f () with
  | r -> restore (); r
  | exception e -> restore (); raise e
