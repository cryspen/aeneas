open Values
open Expressions
open Contexts

(** Translate an interpreter-native [Event.t] into the corresponding
    [CertEvent.event]. Returns [None] when:
    * the event has no cert representation (typically because operands
      reference globals or other shapes the cert can't lift), or
    * the event's migration has not landed yet (commits 3-9 grow this
      function one variant at a time).

    Commits 3-9 of the observer-refactor migration sequence each
    extend this with new [Event.X -> CertEvent.EvX] cases. -*)
let event_to_cert (ctx : eval_ctx) (ev : Event.t) : CertEvent.event option =
  match ev with
  | Event.Copy { src; dst } ->
      (* The src/dst arrive as a single [place] from the interpreter,
         already paired. Translation fails when the place references a
         global; the inline emit site used to elide it then, so we do
         the same. *)
      (match CertEvent.cert_place_of_place src,
             CertEvent.cert_place_of_place dst with
       | Some cp_src, Some cp_dst ->
           Some (CertEvent.EvCopy { src = cp_src; dst = cp_dst })
       | _ -> None)
  | Event.Move { src; dst } ->
      (match CertEvent.cert_place_of_place src,
             CertEvent.cert_place_of_place dst with
       | Some cp_src, Some cp_dst ->
           Some (CertEvent.EvMove { src = cp_src; dst = cp_dst })
       | _ -> None)
  | Event.Reborrow { child; parent; place; parent_live; parent_abs } ->
      (match CertEvent.cert_place_of_place place with
       | Some cp ->
           Some (CertEvent.EvReborrow {
             child; parent; place = cp; parent_live; parent_abs;
           })
       | None -> None)
  | Event.SymExpandMutBorrow
      { sv_id; bid; inner_sv; parent_abs; subst_locals; subst_loans } ->
      Some (CertEvent.EvSymExpandMutBorrow {
        sv_id; bid; inner_sv; parent_abs; subst_locals; subst_loans;
      })
  | Event.MutBorrow { loan; place; value } ->
      (match CertEvent.cert_place_of_place place with
       | Some cp ->
           let symval : symbolic_value_id =
             match value.value with
             | VSymbolic sv -> sv.sv_id
             | _ -> SymbolicValueId.of_int 0
           in
           (* M9.6 (Option C) — subsumes M9.5w + M9.5aa. Place
              projection contains a [Deref] ⇒ MbkInAbsReborrow (the
              caller-input abs owns the borrow's lifetime; absId is a
              placeholder until the AbsRegistry lands). No [Deref]
              but we're inside an open loop body ⇒ MbkLoopOwned with
              the topmost loop id from the cert loop stack.
              Otherwise ⇒ MbkDirect. *)
           let has_deref =
             List.exists
               (fun (pe : projection_elem) ->
                 match pe with Deref -> true | _ -> false)
               cp.cp_projection
           in
           let kind_hint : CertEvent.cert_mut_borrow_kind =
             if has_deref then
               CertEvent.MbkInAbsReborrow (AbsId.of_int 0)
             else
               match !(ctx.cert_loop_id_stack) with
               | top :: _ -> CertEvent.MbkLoopOwned top
               | [] -> CertEvent.MbkDirect
           in
           Some (CertEvent.EvMutBorrow {
             loan; place = cp; symval; kind_hint;
           })
       | None -> None)
  | _ ->
      (* Other variants are migrated in commits 4-9. *)
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
