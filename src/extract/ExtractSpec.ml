(** Lean printer for {!Spec.t} entries. *)

module F = Format

(** Emit one [Spec.spec] entry. *)
let emit_spec ctx fmt (s : Spec.spec) =
  match s.kind with
  | HaxSpec hs -> ExtractHaxSpecs.emit_spec ctx fmt hs s.span

(** Emit one [Spec.proof_obligation] entry. *)
let emit_proof_obligation ctx fmt (o : Spec.proof_obligation) =
  match o.kind with
  | HaxProof ho -> ExtractHaxSpecs.emit_obligation ctx fmt ho o.span

let extract_specs (ctx : ExtractBase.extraction_ctx) fmt =
  if not (List.is_empty ctx.specs) then begin
    F.pp_print_break fmt 0 0;
    F.pp_print_string fmt "open Std.Do";
    F.pp_print_cut fmt ();
    List.iter (emit_spec ctx fmt) ctx.specs
  end

let extract_proof_obligations (ctx : ExtractBase.extraction_ctx) fmt =
  List.iter (emit_proof_obligation ctx fmt) ctx.proof_obligations
