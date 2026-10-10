(** Dispatcher from the generic {!Spec} IR to the concrete spec printer.

    Currently, guarded by a config flag to be only for the Lean backend. *)

module F = Format

(** Emit one [Spec.spec] entry. *)
let emit_spec ctx fmt (s : Spec.spec) =
  match s.kind with
  | HaxSpec hs -> ExtractHaxSpecs.emit_spec ctx fmt hs s.span

(** Emit one [Spec.proof_obligation] entry. *)
let emit_proof_obligation ctx fmt (o : Spec.proof_obligation) =
  match o.kind with
  | HaxProof ho -> ExtractHaxSpecs.emit_obligation ctx fmt ho o.span

(** Register the names generated for the specs and proof obligations. Must be
    called after registering the crate items: clashes are reported as errors. *)
let register_names (ctx : ExtractBase.extraction_ctx) :
    ExtractBase.extraction_ctx =
  let ctx =
    List.fold_left
      (fun ctx (s : Spec.spec) ->
        match s.kind with
        | HaxSpec hs -> ExtractHaxSpecs.register_spec_names ctx s.id hs)
      ctx ctx.specs
  in
  List.fold_left
    (fun ctx (o : Spec.proof_obligation) ->
      match o.kind with
      | HaxProof ho -> ExtractHaxSpecs.register_obligation_names ctx o.id ho)
    ctx ctx.proof_obligations

let extract_specs ctx fmt = List.iter (emit_spec ctx fmt) ctx.specs

let extract_proof_obligations ctx fmt =
  List.iter (emit_proof_obligation ctx fmt) ctx.proof_obligations
