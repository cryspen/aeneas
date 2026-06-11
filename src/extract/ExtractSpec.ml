(** Lean printer for {!Spec.t} entries. *)

module F = Format

(** Emit one [Spec.spec] entry. *)
let emit_spec ctx fmt (s : Spec.spec) =
  match s.kind with
  | HaxSpec hs -> ExtractHaxSpecs.emit_spec ctx fmt hs s.span

let extract_specs (ctx : ExtractBase.extraction_ctx) fmt =
  if not (List.is_empty ctx.specs) then begin
    F.pp_print_break fmt 0 0;
    F.pp_print_string fmt "open Std.Do";
    F.pp_print_cut fmt ();
    List.iter (emit_spec ctx fmt) ctx.specs
  end
