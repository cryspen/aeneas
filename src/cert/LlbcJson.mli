(** M9.7d: minimal Aeneas-side LLBC -> JSON serializer for cert v3.

    Mirrors {!Charon.Generated_OfJson} in reverse but only emits the
    subset of the LLBC subtree the Lean parser
    ({!AeneasCheck.Json.Parser.parseLlbcProgram} in
    [aeneas-lean-checker/AeneasCheck/Json/Parser.lean]) actually
    consumes. Everything we don't structure is left as [`Null] or a
    stringified [TOpaque "<repr>"] fallback, matching what
    [parseLlbc*] tolerates.

    Why an Aeneas-side serializer? Charon's [charon-ml] crate only
    ships deserializers ([OfJson.ml], [Generated_OfJson.ml]); there is
    no upstream [crate_to_json] mirror. Adding one would require a
    charon-pin bump. We picked the contained-blast-radius route: stay
    on the existing pin, ship a minimal serializer here that targets
    only what the Lean checker reads, and revisit if Phase E ever
    needs richer shapes.

    The top-level entry produces the JSON shape the Lean
    [parseLlbcProgram] expects, suitable for embedding under the
    [llbc_program] key of cert v3. *)

val crate_to_json : LlbcAst.crate -> Yojson.Basic.t
(** Serialize an Aeneas {!LlbcAst.crate} into the JSON shape the Lean
    checker's [parseLlbcProgram] consumes. *)
