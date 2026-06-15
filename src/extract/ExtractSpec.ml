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

let extract_specs ctx fmt = List.iter (emit_spec ctx fmt) ctx.specs

let extract_proof_obligations ctx fmt =
  List.iter (emit_proof_obligation ctx fmt) ctx.proof_obligations

(** The manifest JSON [{ "proof_obligations": [ "<fn>.spec.proof", ... ] }],
    built from the names {!ExtractHaxSpecs} actually emitted (not re-derived). *)
let proof_obligations_manifest_json () : Yojson.Safe.t =
  let names =
    match !Config.opt_spec_config with
    | Some(Hax, _) -> ExtractHaxSpecs.get_emitted_obligation_names ()
    | _ -> []
  in
  `Assoc [ ( "proof_obligations", `List (List.map (fun n -> `String n) names) ); ]
