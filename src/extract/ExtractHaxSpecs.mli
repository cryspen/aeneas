(** Lean printer for {!HaxSpec.spec} entries. *)

module F = Format

(** Emits a [HaxSpecs.proof] entry. *)
val emit_proof : F.formatter -> HaxSpecs.proof -> unit

(** Emits one [HaxSpecs.spec] entry. The [span option] is used for errors *)
val emit_spec :
  ExtractBase.extraction_ctx ->
  F.formatter ->
  HaxSpecs.spec ->
  Meta.span option ->
  unit

(** Emits one [HaxSpecs.obligation] entry. The [span option] is used for errors
*)
val emit_obligation :
  ExtractBase.extraction_ctx ->
  F.formatter ->
  HaxSpecs.obligation ->
  Meta.span option ->
  unit
