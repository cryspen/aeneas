(** Lean printer for {!HaxSpec.spec} entries. *)

module F = Format

(** Emits a [HaxSpecs.proof] entry. *)
val emit_proof : F.formatter -> HaxSpecs.proof -> unit

(** Emits one [HaxSpecs.t] entry. The [span option] is used for error reporting
    when the spec refers to an unknown function. *)
val emit_spec :
  ExtractBase.extraction_ctx ->
  F.formatter ->
  HaxSpecs.t ->
  Meta.span option ->
  unit
