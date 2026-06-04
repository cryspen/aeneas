(** Lean printer for {!Spec.t} entries. *)

module F = Format

(** Emit one [Spec.t] entry. *)
let emit_spec (ctx : ExtractBase.extraction_ctx) (fmt : F.formatter)
    (s : Spec.t) : unit =
  ignore (ctx, fmt, s);
  ()

let extract_specs (ctx : ExtractBase.extraction_ctx) (fmt : F.formatter) =
  if not (List.is_empty ctx.specs) then begin
    F.pp_print_break fmt 0 0;
    F.pp_print_string fmt "open Std.Do";
    F.pp_print_cut fmt ();
    List.iter (emit_spec ctx fmt) ctx.specs
  end
