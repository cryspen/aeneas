# Pure-IR JSON Export — Workplan

A self-contained plan to add a JSON dump of Aeneas's Pure IR at any
stage after `SymbolicToPure`, plus a Rust crate that parses the
JSON and is the foundation for new Aeneas backends written in Rust.

> **Scope discipline:** this plan is *independent* of the Lean
> cert-checker, the soundness proof, and the Z2/Z3a/Z4a trust-removal
> work. It touches only `src/` (OCaml side) and a new `rust/pure-ir/`
> crate. The Lean tree is read-only for this campaign.

---

## Goal

After this campaign:

1. Aeneas accepts `-dump-pure-ir <stage>:<dest>` where `<stage>` is
   one of `post-s2p`, `post-micro`, `pre-extract`. The flag writes a
   per-crate JSON file capturing the full `translated_crate` state at
   that stage.
2. A new Rust crate `rust/pure-ir/` parses the JSON into a
   strongly-typed Rust AST and exposes it as a library. The crate
   has zero dependencies on Aeneas's OCaml side at build time.
3. CI runs the dump on all 89 fixtures at all three stages and
   verifies the Rust crate parses every output cleanly.

The Rust AST is the foundation for writing new Aeneas backends
(C, F\*-via-Karamel, Coq, pretty-printers, IDE integrations) in Rust
without re-implementing the symbolic-interpretation pipeline.

---

## Non-goals

* **Re-importing JSON back into OCaml.** We don't write a fromJson
  function in OCaml. See *Round-trip decision* below.
* **Loading the JSON into Lean.** Future work; not blocked by this.
* **Replacing Aeneas's existing backends.** They keep working.
* **Verifying the dump.** This is an unverified producer/consumer
  pair. Trust shifts to "Aeneas → JSON is faithful" (testable via
  golden), and the Rust crate is plain Rust (no proof obligation).

---

## Round-trip decision

**The plan is one-way: OCaml writes JSON; Rust reads JSON. No OCaml
`fromJson`. No round-trip.**

Reasoning:

1. **The consumer is Rust.** Symmetric `fromJson`/`toJson` in OCaml
   is dead code if nothing in OCaml ever reads its own dump.
2. **Round-trip catches schema bugs but isn't the only way to catch
   them.** Golden-test the OCaml output (commit small fixture
   outputs verbatim) and the Rust parse (commit a structural dump
   of the parsed AST). If both goldens stay in sync, the schema is
   self-consistent.
3. **`Pure.expr` has OCaml-side internals that don't round-trip
   cleanly** — fresh-id generators, `[@opaque]` span fields,
   internal mutability for memoised name resolution. Writing
   `fromJson` would require pretending these are inert, then
   regenerating them on load. Brittle.
4. **The cost is half the schema work.** ~135 constructors in
   `Pure.expr` (plus `Pure.type_decl`, `Pure.fun_sig`, etc.) — every
   one needs an encoder. Doubling that for decoders we never call
   is wasteful when the Rust side will write its own decoder anyway.

**When we would reconsider round-trip:** if/when we add an
`aeneas -from-pure-ir` consumer in OCaml (the original Phase 1
sketch). At that point fromJson + round-trip gets justified by an
actual consumer. Until then, skip.

What replaces round-trip:

* **Golden fixtures.** Commit 3–5 small fixture JSON outputs (one per
  pipeline stage). Any schema drift produces a goldenfile diff that
  CI catches.
* **Rust-side structural test.** For each of the 89 fixtures, the
  Rust crate parses the JSON, walks the AST, and emits a
  byte-stable structural summary (e.g. "fixture `incr_cert`:
  1 fn_decl, 3 lets, 1 binop, …"). Commit the summary; diff in CI.
  This catches both producer and consumer regressions.

---

## Architecture

### OCaml side: `src/pure/PureJson.ml{,.mli}`

Single new module. Pattern follows `src/cert/CertJson.ml` (the
existing cert-event serializer):

* Tagged-enum convention matching Charon's Serde default — nullary
  variants are JSON strings; payload variants are `{"Variant":
  payload}` objects.
* Output is one-way (OCaml → JSON only).
* Re-uses identifier-encoding helpers from `CertJson.ml` (or
  generalises them).

Surface:

```ocaml
(* PureJson.mli *)
open Pure

val crate_to_json : translated_crate -> Yojson.Basic.t
val fun_decl_to_json : fun_decl -> Yojson.Basic.t
val type_decl_to_json : type_decl -> Yojson.Basic.t
val global_decl_to_json : global_decl -> Yojson.Basic.t
val trait_decl_to_json : trait_decl -> Yojson.Basic.t
val trait_impl_to_json : trait_impl -> Yojson.Basic.t
(* expr / texpr / ty / pattern / etc. exposed too for partial dumps *)
val expr_to_json : expr -> Yojson.Basic.t
val texpr_to_json : texpr -> Yojson.Basic.t
val ty_to_json : ty -> Yojson.Basic.t
```

### OCaml side: CLI hook

In `src/Config.ml`:

```ocaml
(* New flag: -dump-pure-ir <stage>:<dest>.
   <stage> is one of: post-s2p, post-micro, pre-extract.
   <dest> is a path; the writer creates one .pure.json per crate. *)
val dump_pure_ir : (string * string) option ref
```

In `src/Main.ml`, parse the flag.

In `src/Translate.ml`:

* After `translate_crate_to_pure` returns, if `stage = post-s2p`,
  dump.
* In `apply_passes_to_pure_fun_translations`, if `stage = post-micro`,
  dump after the pass loop.
* Just before `Extract.extract_*` calls, if `stage = pre-extract`,
  dump.

The dump call is uniformly:

```ocaml
let dump_if_stage requested_stage actual_stage tc =
  match !Config.dump_pure_ir with
  | Some (s, dest) when s = actual_stage ->
      let json = PureJson.crate_to_json tc in
      let oc = open_out (Filename.concat dest (crate_name tc ^ ".pure.json")) in
      Yojson.Basic.pretty_to_channel oc json;
      close_out oc
  | _ -> ()
```

### Rust side: `rust/pure-ir/`

New Cargo crate. Layout:

```
rust/pure-ir/
├── Cargo.toml
├── src/
│   ├── lib.rs           # crate root, re-exports
│   ├── ast.rs           # the AST types (one per Pure.ml type)
│   ├── parser.rs        # serde_json → AST
│   └── walk.rs          # visitor traits, basic walks
├── tests/
│   ├── parse_fixtures.rs   # round-trip parse 89 fixtures
│   └── golden_summary.rs   # structural-summary golden test
└── fixtures/
    └── (committed JSON samples per stage)
```

Dependencies (minimal):

* `serde` + `serde_json` for parsing.
* `thiserror` for error types.

The AST is hand-written, one Rust type per Pure.ml type, mirroring
the OCaml constructor names. Serde tag = "internally-tagged"
matching the OCaml emit's `{"Variant": payload}` convention.

Example:

```rust
// rust/pure-ir/src/ast.rs

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Expr {
    FVar(FVarId),
    BVar(BVar),
    CVar(ConstGenericVarId),
    Const(Literal),
    App(Box<TExpr>, Box<TExpr>),
    Lambda(TPat, Box<TExpr>),
    Qualif(Qualif),
    Let(bool, TPat, Box<TExpr>, Box<TExpr>),
    Switch(Box<TExpr>, SwitchBody),
    Loop(Box<Loop>),
    StructUpdate(StructUpdate),
    Meta(EMeta, Box<TExpr>),
    EError(Option<Span>, String),
}

#[derive(Debug, Clone, serde::Deserialize)]
pub struct TExpr {
    pub e: Expr,
    pub ty: Ty,
}

// ... etc for Ty, Qualif, Loop, StructUpdate, ...
```

The `kind`/`payload` tagging means the OCaml emit must produce a
fixed shape; deviation = parser error.

### Versioning

The dumped JSON's root carries:

```json
{
  "pure_ir_fmt_version": 2,
  "stage": "post-s2p" | "post-micro" | "pre-extract",
  "crate_name": "...",
  "type_decls": [...],
  "fun_decls": [...],
  "trait_decls": [...],
  "trait_impls": [...],
  "global_decls": [...]
}
```

`pure_ir_fmt_version` bumps on any schema change. The Rust parser
rejects unknown versions with a clear error.

---

## Implementation phases

### Phase 1 — minimal stub (≤1 day)

1. Add `src/pure/PureJson.ml{,.mli}` with `crate_to_json` covering
   only literals + the smallest expression: `Pure.expr` variants
   `FVar`/`BVar`/`Const`/`App`. Stub-out everything else as
   `\`Assoc [("UNSUPPORTED", \`String "TODO")]`.
2. Add `-dump-pure-ir post-s2p:<dest>` flag.
3. Create `rust/pure-ir/` crate scaffold with a parser for the same
   minimal subset.
4. Round-trip the simplest fixture (`incr_cert`) end-to-end: Aeneas
   dumps, Rust parses, Rust prints. Verify by eye.

Acceptance: one fixture parses cleanly. CI not yet wired.

### Phase 2 — full constructor coverage (3–5 days) — landed

Cover every `Pure.expr` constructor + every `Pure.ty` constructor +
`fun_decl` + `type_decl` envelope. Mechanical pattern: one match arm
per OCaml constructor → one serde-tag-matching JSON shape on the
Rust side.

Sequence to minimise breakage:

1. `Ty`: all variants (`TAdt`/`TVar`/`TLiteral`/`TArrow`/etc.)
2. `Literal`, `Qualif`, `TPat`/`Pattern`.
3. `Expr`: `Lambda`, `Let`, `Switch`, `Loop`, `StructUpdate`.
4. `Meta`, `EError`.
5. Envelope: `FunDecl`, `FunBody`, `FunSig`, `TypeDecl`,
   `TraitDecl`, `TraitImpl`, `GlobalDecl`, `TranslatedCrate`.

Per constructor: ~5 LOC OCaml + ~3 LOC Rust + a 1-line entry in the
fixture-coverage matrix.

Acceptance: all 89 fixtures parse on the `post-s2p` stage. No
"UNSUPPORTED" stubs remain in `PureJson.ml`.

**What landed (May 2026):**

- `src/pure/PureJson.ml{,.mli}` was rewritten end-to-end: every
  constructor of `Pure.ty`, `Pure.literal`, `Pure.qualif`,
  `Pure.tpat`/`Pure.pat`, `Pure.binop`/`Pure.unop`, and `Pure.expr`
  is now encoded. The decl envelope covers the real `FunSig`
  (generics, explicit_info, known_info, preds, inputs, output,
  fwd_info, back_effect_info), `FunBody` with real `tpat list`
  inputs, `FunDecl` (loop_id, loop_pos, builtin_info-as-tag, src,
  backend_attributes, signature, body), `TypeDecl`
  (Struct/Enum/Opaque), `GlobalDecl`, `TraitDecl`, `TraitImpl`, and
  the generic `'a binder`.
- `rust/pure-ir/src/ast.rs` mirrors that emit one-for-one. Phase-1
  stub structs are replaced. Recursive `Expr` payloads are `Box`-ed
  to keep the type finite-sized.
- `rust/pure-ir/src/parser.rs` now disables serde_json's default
  128-level recursion guard and uses `serde_stacker` to handle
  deeply-nested expression chains (notably `curve25519`'s let/app
  cascades).
- `rust/pure-ir/tests/parse_all_fixtures.rs` (new): walks all 89
  `tests/llbc/*.llbc` fixtures, spawns `bin/aeneas
  -dump-pure-ir post-s2p:<tmp>`, asserts the dump contains no
  `"UNSUPPORTED"` substring, and parses each via `pure_ir::parse`.
  89/89 fixtures pass. Three (`closures`, `raw_pointers`,
  `issue-804-closure-return-ref`) are `known-failure` /
  `[!lean] skip` in the harness; aeneas exits non-zero after partial
  translation but the dump is still written and parses cleanly.
- Per the plan's defaults, spans, `item_meta`, `llbc_generics`, and
  `mplace` are stripped from the emit. `emeta` and `builtin_info`
  variant payloads are summarised by their tag (the Rust consumer
  has no need for their internal structure yet). The decisions are
  documented in `src/pure/PureJson.mli`.

**Spans + attributes campaign (May 2026) — fmt v1 → v2:**

The plan-level "Risks" entry below originally proposed a
`-dump-pure-ir-with-spans` flag to opt into source meta. We went
always-on instead: the dump grows ~2-3× but every consumer gets the
same payload, no schema fork. `pure_ir_fmt_version` bumped from 1 to 2.

What now rides along on every dump:

- `item_meta` on every decl (`fun_decl`, `type_decl`, `global_decl`,
  `trait_decl`, `trait_impl`) — carries `name` (a structured
  `path_elem[]`), `span`, `source_text`, `attr_info` (attributes,
  inline, rename, public), `is_local`, `opacity`, and `lang_item`.
- `loop.span` is now emitted alongside the loop payload.
- The `Meta of emeta * texpr` expression node ships the full `emeta`
  payload — including the `mplace` structures embedded in
  `Assignment` / `SymbolicAssignments` / `SymbolicPlaces` / `MPlace`.
  `mplace` itself is a recursive sum (`PlaceLocal` / `PlaceGlobal` /
  `PlaceProjection`).
- `EError`'s optional `Meta.span` is no longer stripped.

The span shape matches `CertJson.json_cert_source_span` verbatim
(`{file, beg_line, beg_col, end_line, end_col}`) so any future
consumer can share a parser. Charon `path_elem`'s heavy variants
(`PeImpl`, `PeInstantiated`) opaque-encode (tag only) to keep the
schema bounded; `PeIdent` and `PeTarget` carry full payloads.

Rust mirrors: new `Span`, `AttrInfo`, `Attribute`, `InlineAttr`,
`RawAttribute`, `ItemMeta`, `PathElem`, `MPlace`, `MProjectionElem`,
`FieldProjKind`, plus a real `EMeta` enum replacing the Phase-2
stub. `SUPPORTED_FMT_VERSION` bumped to 2. A new test
`parse_spans_and_attrs.rs` asserts every `fun_decl` has a populated
`item_meta.span.file` + non-zero `beg_line`, and that the `derive`
fixture round-trips a non-empty `AttrDocComment` list end-to-end.
The 89-fixture sweep stays green at v2.

### Phase 3 — additional stages + tests (2 days) — landed

1. Wire `post-micro` and `pre-extract` dump points in
   `Translate.ml`.
2. Generate fixtures at all 3 stages for the 89 fixtures (89 × 3 =
   267 JSON files; commit a small representative subset, ignore the
   rest in `.gitignore`).
3. Golden tests:
   * OCaml golden: commit `pure-ir/golden/incr_cert.post-s2p.json`
     + `incr_cert.post-micro.json` + `incr_cert.pre-extract.json`
     (3 files). CI fails on diff.
   * Rust golden: commit
     `rust/pure-ir/tests/golden/incr_cert.summary.txt` (one line per
     fixture: counts of decls, constructors, etc.). CI fails on
     diff.
4. CI:
   * `cargo build && cargo test` in `rust/pure-ir/`.
   * `make dump-pure-ir-sweep` walks all 89 fixtures × 3 stages,
     verifies every output parses on the Rust side.

Acceptance: full CI integration. 89 × 3 = 267 JSON files all
parseable. Goldens stable.

**What landed (May 2026):**

- `src/Translate.ml` was refactored to expose a true post-S2P hook
  point. `translate_crate_to_pure` now accepts an optional
  `post_s2p_hook` callback that fires inside the function, between
  the symbolic-to-pure pass and the micro-pass loop, with the raw
  `Pure.fun_decl list`. `translate_crate` wires three callers:
  - **`post-s2p`** — fires from the new callback, capturing the
    pre-micro IR.
  - **`post-micro`** — fires right after `translate_crate_to_pure`
    returns. The IR has been simplified and loop bodies extracted
    into separate `fun_decl`s; the dump flattens the main fn plus
    loop-aux fns into one list.
  - **`pre-extract`** — fires immediately before
    `extract_translated_crate`. Same IR shape as `post-micro`, but
    kept as a separate stage so future passes inserted between
    micro and extract have a clearly-named pinpoint.
- All three stages write `<crate>.pure.json` to `<dest>`; the
  `"stage"` field inside the JSON disambiguates. The `failwith` for
  unimplemented stages is gone.
- `rust/pure-ir/tests/parse_all_fixtures.rs` was extended into a
  three-stage sweep (renamed test fn:
  `sweep_all_fixtures_all_stages`). 89 fixtures × 3 stages = 267
  aeneas spawns, all green. Wall time ~100s.
- `rust/pure-ir/tests/parse_goldens.rs` (new): 5 fixtures × 3 stages
  = 15 committed goldens under `rust/pure-ir/tests/golden/`. Picked
  to span the IR shapes the sweep tests in bulk:
  - `incr_cert` (trivial body, mut-borrow forward+backward)
  - `loops_simple` (loop decomposition; visible 1→2 fun_decl growth
    across stages)
  - `traits_basic` (trait + impl)
  - `enums_basic` (enum payload variants)
  - `arrays_defs` (array ops; the larger `arrays.llbc` was rejected
    at 16MB JSON — too big to commit)
  Goldens regenerate via `PURE_IR_BLESS=1 cargo test --test
  parse_goldens`. The test normalises `item_meta.span.file`
  (strips everything up to and including `tests/src/` / `tests/llbc/`)
  before comparing, so goldens don't diff per machine.
- `Makefile` got a new `dump-pure-ir-sweep` target (depends on
  `build-bin-dir`) that runs all four pure-ir crate tests. Not yet
  wired into the GH Actions workflow — the existing `.github/
  workflows/ci.yml` runs everything through `nix build`, and the
  `aeneas-tests` derivation in `flake.nix` would need to grow a
  separate Rust-toolchain step to invoke the cargo tests on the
  `rust/pure-ir/` crate. Left to a follow-up; the `gmake` target
  is the manual entry point.

### Phase 4 — first backend prototype (89-fixture sweep landed)

The natural follow-on: build one Rust-side consumer of the JSON that
emits something useful. Plan (I) (per the design discussion) was
chosen — consume the JSON, emit IR-faithful Rust source — over an
in-tree `-emit-rust-model` flag on the OCaml side. The OCaml pipeline
stays out of scope.

**What landed (May 2026):**

- New crate `rust/pure-ir-emit-rust/` and a top-level workspace
  `rust/Cargo.toml` listing both `pure-ir` and `pure-ir-emit-rust`
  as members.
- `pure_ir_emit_rust::emit_crate(&TranslatedCrate, &EmitOptions) ->
  String` turns a parsed Pure-IR crate into a single Rust source
  file. The emit is intentionally NOT a byte-for-byte recovery of the
  original `.rs` — symbolic-to-pure has functionalised mutable
  borrows (`incr(x: &mut u32)` becomes `incr(x: u32) -> Result<u32>`),
  fused loops into a body decl reachable via a fixed-point
  combinator, and threaded `Result` through fallible operations.
  The output targets two invariants only: (1) `rustc --edition 2021
  --crate-type lib --emit metadata` accepts it, and (2) one Rust
  construct per Pure-IR node, no folding back into idiomatic Rust.
- CLI binary `pir2rs <input.pure.json> [-o out.rs]` parses a JSON
  dump and writes the emitted Rust to stdout / `-o`.
- A tiny `aeneas_runtime` prelude is emitted at the top of every
  output file: a `Result<T> = core::result::Result<T, ()>` alias,
  `ret`/`fail` shorthands, and a `loop_op` stub for the loop
  fixed-point combinator. Keeps the per-expr emit clean.
- De-Bruijn variables are resolved via a stack of binder scopes
  threaded through every expression-emit function. Generic params
  resolve via a separate `GenCtx` populated from the surrounding
  `FunDecl.signature.generics` / `TypeDecl.generics`.
- Unhandled variants degrade to `unimplemented!(<msg>)` (with the
  right type ascription so the surrounding `?` still typechecks),
  keeping the output parseable.
- Tests:
  - `pure-ir-emit-rust/tests/emit_incr_cert.rs` — four-test focused
    integration test: emit at each of the three pipeline stages, plus
    a content-shape assertion that both `incr` and `incr_local`
    appear in the post-s2p emit.
  - `pure-ir-emit-rust/tests/compile_check.rs` — **full 267-pair
    sweep**: for every `tests/llbc/*.llbc` fixture at every pipeline
    stage (`post-s2p`, `post-micro`, `pre-extract`), call aeneas to
    dump the JSON, emit Rust, and shell out to `rustc --emit
    metadata`. Pairs we can't emit faithfully today are listed in a
    `KNOWN_GAPS` table with a one-line reason and are skipped (but
    logged on stderr); everything else MUST compile.

**Sweep coverage (after the extension):**

| | count |
|--|--|
| Total (fixture × stage) pairs | 267 |
| `rustc`-accepted emits | **175 (≈ 66 %)** |
| Fixtures with all three stages green | **50 / 89 (≈ 56 %)** |
| `KNOWN_GAPS` entries (skipped, reported) | 92 |
| Unexpected failures (test panics) | 0 |

The 92 known gaps cluster into a small set of structural
limitations:

| Class | ≈ count | Why it's hard |
|--|--|--|
| `move-of-FnOnce-backward-fn` | ~25 | Aeneas re-uses backward fns across branches; `Box<dyn FnOnce>` is consumed on first call. |
| `loop_op-positional-arg-mismatch` | ~25 | `LoopOp` shim has a fixed shape (`F: FnOnce(T) -> Result<T>`); IR sites pass diverse arities. |
| `trait-method-* placeholder` | ~20 | `Qualif::FunOrOp(_, TraitMethod(_))` collapses to `unimplemented!()` — many fixtures call stdlib traits. |
| `destructure-Box-{LCell,multi-binder}` | ~10 | Stable Rust has no `box` patterns; recursive ADT field destructure can't pierce a `Box<Self>`. |
| `type-changing-struct-update` | ~3 | Aeneas `..init` can change generic args; Rust struct-update requires identical types. |
| Miscellaneous (curve25519 size, FFI `fmt::Arguments` shape, etc.) | ~10 | One-offs. |

The full table lives in `rust/pure-ir-emit-rust/tests/compile_check.rs`
(`KNOWN_GAPS` constant) — each entry carries a short reason string
that survives the sweep output.

### Phase 4a — shim routing via `core-models` (Option A landed)

After Phase 4, the `pir2rs` emit produced syntactically valid Rust
but a large class of fns (~108 candidates the auto-gen diff filter
skipped) transitively reached opaque shims:

```rust
pub fn impl_core_num_wrapping_add_23(p0: impl Sized, p1: impl Sized) -> u32 {
    unimplemented!("opaque body")
}
```

These shims are the emitter's collapse of every opaque / trait-method
call to a uniform placeholder. The values they were supposed to
return are well-defined (`u32::wrapping_add`, `Default::default()`,
`u32::BITS`, …) — they just need real bodies.

**Option A (test-side post-processor) landed:**

- New module `pure_ir_emit_rust::core_models_map` maps Charon paths
  (`["core", "num", "wrapping_add"]`, ...) to a `ShimRoute` describing
  the rewritten body. Coverage targets the cases the existing committed
  models need (`core::num::*::{wrapping,saturating,rotate,count_ones,
  leading_zeros,pow,abs,rem_euclid,BITS,MIN,MAX}`,
  `core::default::default`, `core::cmp::{min,max}`).
- New binary `route-shims` reads a `pir2rs` emit + the originating
  `pure.json`, looks up each opaque shim's path in the map, and
  rewrites both the signature (`impl Sized` → IR-recovered concrete
  type) and the body (`unimplemented!()` → `<ret_ty>::method(...)`).
  Refuses to touch shims with generic params / where-clauses (those
  need per-callsite monomorphisation info Option C will provide).
- `regen-diff-models.sh` now invokes `route-shims` per fixture after
  `pir2rs`. 13 model files updated on the first run; the diff harness
  un-ignored 2 tests (`compare_simple::add_u32`, `demo::mod_add`)
  that previously panicked on the placeholder. Auto-gen test count
  rose from 40 → 42 (new blocks: `calls::pick`, `compare_simple::
  add_u32`).
- **The emitter library is unchanged.** `emit::emit_crate` still
  produces the same `impl Sized` + `unimplemented!()` shapes for
  every opaque decl; the rewrite happens in the post-processor.
  This is the Option-A boundary.

**Privacy gotcha:** `core_models::num::<t>::wrapping_add` and friends
are declared without `pub` inside `#[hax_lib::attributes]` impl
blocks, so they're not callable from outside the `core-models`
crate. The map routes through native Rust methods
(`<t>::wrapping_add`) and free fns
(`rust_primitives::arithmetic::wrapping_add_<t>` would be the
public-callable equivalent inside the `core-models` workspace).
Observationally identical:
`core_models::num::<t>::wrapping_add` forwards to
`rust_primitives::arithmetic::wrapping_add_<t>`, which is
`x.wrapping_add(y)` — i.e. the same thing.

### Phase 4b — emitter-side routing (Option C, future)

Option C graduates the path map into `emit.rs` itself, so the emit
stage produces routed bodies directly (no post-processor). This
unblocks:

- Routing shims that carry generic params (`<T>`, `<T, A>`, ...)
  with full per-callsite monomorphisation context.
- Cases where `core-models` has the routing target but the post-
  processor can't safely rewrite (where-clauses, complex generic
  arity, ...). Option C has the IR's signature context at emit time
  and so can render the right turbofish.
- A first step toward extracting Aeneas-Rust-emitted code as a
  drop-in `core::*` model in downstream verified-Rust pipelines.

The path is staged:

1. **Phase 4a (landed):** `core_models_map` lives in the lib but is
   unused by `emit_crate`. Post-processor handles the rewrite.
2. **Phase 4b/Option C:** `emit_crate` consults `core_models_map`
   when lowering opaque fns. The post-processor binary is retired.
   `core-models` becomes a `[dependencies]` entry (not just dev-).

---

## Phase 1 in detail (the first concrete commit)

A single commit lands:

* `src/pure/PureJson.ml{,.mli}` — the minimal stub.
* `src/Config.ml` — the `dump_pure_ir` field.
* `src/Main.ml` — the CLI flag parser.
* `src/Translate.ml` — the post-s2p dump call.
* `rust/pure-ir/Cargo.toml` + `src/lib.rs` + `src/ast.rs` +
  `src/parser.rs` — the minimal Rust parser.
* `rust/pure-ir/tests/parse_incr_cert.rs` — single round-trip test.
* `documentation/plans/pure-ir-json-export-plan.md` — this file
  (already on disk).

Manual smoke test in the PR description:

```bash
bin/aeneas -backend lean -dump-pure-ir post-s2p:/tmp/dump \
  tests/llbc/incr_cert.llbc
ls /tmp/dump/   # incr_cert.pure.json
(cd rust/pure-ir && cargo test parse_incr_cert)
```

The test parses the OCaml output and asserts a minimal structural
invariant (e.g. "the crate has 1 fun_decl named `incr`").

---

## Risks

* **`Pure.ml`'s span / source-position fields are noisy.** Every
  expression carries a `Meta.span [@opaque]`. Two options were
  considered:
  * Strip spans from the dump (lossy but simpler).
  * Emit spans as opaque strings (lossless, JSON bloats).
  **Resolved (May 2026):** went always-on, no `-dump-pure-ir-with-spans`
  flag. Bumped `pure_ir_fmt_version` 1 → 2. Spans now ride on every
  decl (`item_meta.span`), every `loop.span`, every `Meta` expression
  payload, and `EError`. JSON grew ~2-3×; acceptable. See the
  Phase-2-landed entry above for the full list of v2 additions.

* **The de-Bruijn index encoding (BVar) is brittle.** `Pure.bvar` is
  a record `{ index : int; name : string option }`. Encode as
  `{"BVar": {"index": N, "name": null}}`. Rust side mirrors.
  Validation: cross-check `Pure.expr_close`/`expr_open` invariants
  via a fuzz test (Phase 3 stretch goal).

* **Trait references chase through `trait_ref` → `trait_decl_id`
  + `generic_args`.** Schema gets nested. Worth pulling the
  trait-reference encoding into its own helper module on both sides.

* **OCaml/Rust constructor-name skew.** If someone renames an OCaml
  constructor in `Pure.ml`, the JSON serde tag silently breaks. CI
  golden test catches this (the OCaml output drifts), but the error
  message can be cryptic. Consider committing a derived
  `pure_ir_schema.json` (JSON Schema spec) and validating both
  encoder + decoder against it.

* **Per-constructor mechanical work multiplied across the surface.**
  ~135 expression constructors + ~30 ty constructors + decl envelope
  = ~200 mechanical pattern matches per side. Each is trivial; the
  total is a few solid days of typing. PPX-derive options
  (`ppx_deriving_yojson_safe`) could automate the OCaml side; the
  trade-off is loss of control over the tagged-enum convention.
  Recommend hand-writing for v1.

---

## What about the Lean cert checker?

Out of scope for this plan. If/when the Lean cert checker also wants
to emit Pure IR JSON (a future Phase 2 of the trust-architecture
sketch), it can reuse the same schema and the same Rust consumer.
That work depends on the cert checker first growing a faithful Pure
IR representation, which is a multi-quarter effort separate from
this campaign (see `llbc-trust-removal-plan.md` and prior session
notes).

---

## Acceptance summary

| Phase | Deliverable | Acceptance | Status |
|---|---|---|---|
| 1 | Minimal OCaml emit + Rust parse | 1 fixture round-trips by eye | done (commit `f950d1fe`) |
| 2 | Full constructor coverage | 89 fixtures parse on `post-s2p` | done (May 2026, 89/89) |
| 2-spans | Always-on spans + `attr_info` (fmt v2) | 89 fixtures still parse; spans + attrs survive end-to-end | done (May 2026) |
| 3 | All stages + CI | 267 JSON files parse; goldens stable | done (May 2026) |
| 4 | First Rust backend prototype (MVP) | `rust/pure-ir-emit-rust/` emits IR-faithful Rust source that `rustc` accepts for a representative fixture set | done (May 2026) |

Phases 1–3 are this campaign. Phase 4 MVP landed alongside; further
backend work launches separate per-backend workstreams.
