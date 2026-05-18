open Contexts

(** Translate an interpreter-native [Event.t] into the corresponding
    [CertEvent.event]. Returns [None] when:
    * the event has no cert representation (typically because operands
      reference globals or other shapes the cert can't lift), or
    * the event's migration has not landed yet (commits 3-9 grow this
      function one variant at a time).

    Commits 3-9 of the observer-refactor migration sequence each
    extend this with new [Event.X -> CertEvent.EvX] cases. -*)
let event_to_cert (_ctx : eval_ctx) (_ev : Event.t) : CertEvent.event option =
  (* Skeleton: no variants migrated yet. Commits 3-9 grow this. *)
  None

let on_event (ctx : eval_ctx) (ev : Event.t) : unit =
  if !(ctx.cert_events_suppressed) then ()
  else
    match event_to_cert ctx ev with
    | None -> ()
    | Some cert_ev ->
        ctx.cert_event_buffer := cert_ev :: !(ctx.cert_event_buffer)

let observer : Observer.observer = { on_event }

let install () : unit = Observer.current := observer
