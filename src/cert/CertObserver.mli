(** Cert-side [Observer.observer] — translates each [Event.t] into the
    appropriate [CertEvent.event] and feeds it into the active
    [eval_ctx]'s [cert_event_buffer].

    Commits 3-9 of the observer refactor migrate the 25 inline emit
    sites in [src/interp/] one file at a time. Each migration extends
    [event_to_cert] with the matching cases and drops the inline
    [ctx_emit_event (CertEvent...)] from the interpreter. Cert output
    stays byte-equal throughout (the same [CertEvent] ends up in the
    same buffer); the indirection is what lets [src/interp/] be
    upstreamed without the [src/cert/] dependency.

    Commit #10 strips [cert_event_buffer] from [eval_ctx] and gives
    [CertObserver] its own buffer; this module's [flush] becomes the
    canonical read for [CertGen]. -*)

(** Install [CertObserver] as [Observer.current]. Idempotent. Call
    when [-emit-cert] is set; the no-op default remains otherwise. -*)
val install : unit -> unit

(** Reset all per-function observer state (event buffer, loop-id
    stack, ended-loan dedupe set). [CertGen] calls this before
    driving the interpreter on each fun_decl. -*)
val reset : unit -> unit

(** Read out the accumulated events in firing order and clear the
    buffer. -*)
val flush : unit -> CertEvent.event list

(** Translate one interpreter event to a [CertEvent.event]. Returns
    [None] when the event has no cert representation (e.g. globals
    that don't lift). -*)
val event_to_cert :
  Contexts.eval_ctx -> Event.t -> CertEvent.event option
