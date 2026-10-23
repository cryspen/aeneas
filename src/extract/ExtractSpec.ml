(** Dispatcher from the generic {!Spec} IR to the concrete spec printer.

    Currently, guarded by a config flag to be only for the Lean backend. *)

module F = Format

(** Emit one [Spec.spec] entry. *)
let emit_spec ctx fmt (s : Spec.spec) =
  match s.kind with
  | HaxSpec hs -> ExtractHaxSpecs.emit_spec ctx fmt hs

(** Emit one [Spec.proof_obligation] entry. *)
let emit_proof_obligation ctx fmt (o : Spec.proof_obligation) =
  match o.kind with
  | HaxProof ho -> ExtractHaxSpecs.emit_obligation ctx fmt ho

(** Register the names generated for the specs and proof obligations. Must be
    called after registering the crate items: clashes are reported as errors. *)
let register_names (ctx : ExtractBase.extraction_ctx) :
    ExtractBase.extraction_ctx =
  let ctx =
    List.fold_left
      (fun ctx (s : Spec.spec) ->
        try
          match s.kind with
          | HaxSpec hs -> ExtractHaxSpecs.register_spec_names ctx s.id hs s.span
        with Errors.CFailure error ->
          (* An exception was raised (the error was already registered):
             ignore it *)
          [%warn_opt_span] error.span
            "Could not generate names for the spec because of previous error";
          ctx)
      ctx ctx.specs
  in
  List.fold_left
    (fun ctx (o : Spec.proof_obligation) ->
      try
        match o.kind with
        | HaxProof ho -> ExtractHaxSpecs.register_obligation_names ctx o.id ho
      with Errors.CFailure error ->
        (* An exception was raised (the error was already registered): ignore
           it *)
        [%warn_opt_span] error.span
          "Could not generate names for the proof obligation because of \
           previous error";
        ctx)
    ctx ctx.proof_obligations

(** Print the entry [x] with [emit], ignoring a [CFailure]: it was normally
    reported when raised, and only drops [x]. The entry is printed in a buffer
    first, so that a partial output (with unclosed boxes) is dropped too. [fmt]
    must be in a vertical box at column 0, as the entries are. *)
let skip_on_failure fmt (emit : F.formatter -> 'a -> unit) (x : 'a) : unit =
  let buf = Buffer.create 1024 in
  let bfmt = F.formatter_of_buffer buf in
  FormatCompat.use_byte_width bfmt;
  let { F.margin; max_indent } = F.pp_get_geometry fmt () in
  F.pp_set_geometry bfmt ~max_indent ~margin;
  F.pp_open_vbox bfmt 0;
  match emit bfmt x with
  | () ->
      F.pp_close_box bfmt ();
      F.pp_print_flush bfmt ();
      List.iteri
        (fun i line ->
          if i > 0 then F.pp_print_cut fmt ();
          F.pp_print_string fmt line)
        (String.split_on_char '\n' (Buffer.contents buf))
  | exception Errors.CFailure _ -> ()

let extract_specs ctx fmt =
  List.iter (skip_on_failure fmt (emit_spec ctx)) ctx.specs

let extract_proof_obligations ctx fmt =
  List.iter
    (skip_on_failure fmt (emit_proof_obligation ctx))
    ctx.proof_obligations
