(** Generic interpreter-observer registry.

    Downstream consumers (today: only [CertObserver] in [src/cert/])
    register an [observer] under [current]; the interpreter calls
    [notify] / [notify_lazy] / [with_suppressed] without knowing what
    the consumer does with the event.

    The [default] observer is a no-op; the un-instrumented binary
    pays one indirection per rule firing and nothing more. -*)

open Contexts

type observer = { on_event : eval_ctx -> Event.t -> unit }

(** No-op observer. Installed as [current] on startup. -*)
val default : observer

(** Currently-installed observer. [CertObserver] swaps this in when
    [-emit-cert] is set; tests / lib clients can install custom
    observers similarly. -*)
val current : observer ref

(** Fire an event. The common case: the payload is cheap to build
    (a [place], a [borrow_id], a [tvalue]) so the call site
    materialises it eagerly. -*)
val notify : eval_ctx -> Event.t -> unit

(** Fire an event whose payload requires a non-trivial walk of the
    [eval_ctx] (region-abs role extraction, loan-registry collection,
    state-summary build). The thunk is forced only when the installed
    observer is non-default — the no-op pays nothing. -*)
val notify_lazy : eval_ctx -> (unit -> Event.t) -> unit

(** Run [f] with observer notifications suppressed. Used by the loop
    fixed-point computation in [InterpLoopsFixedPoint], where the
    fixpoint iterates the loop body multiple times but only the
    post-fixpoint trace should be observed. The suppression is
    observer-local; the interpreter just hands [f] off. -*)
val with_suppressed : eval_ctx -> (unit -> 'a) -> 'a
