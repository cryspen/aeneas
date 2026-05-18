# Meta-Harness Contract — Project-Agnostic Differential Testing for Aeneas

*Status: design only; no implementation in this document.*
*Audience: a future agent or engineer who has never seen this repo.*
*Companion docs: `differential-testing-plan.md` (gate definitions
G_byte / G_rust / G_lean / G_rfl) and `differential-testing-progress.md`
(through Session 7). This doc does not restate those — it builds on them.*

## 1. Goal

The Aeneas compiler turns a Rust crate into pure Lean (and into other
artifacts: emitted Rust, a `.cert.json` trace, eventually F\*/Coq/HOL4).
For a *fixed* set of fixtures in this repo's `tests/src/*.rs` we already
have ad-hoc differential harnesses that exercise the four gates defined
in `differential-testing-plan.md`. **The meta-harness is the same
machinery, but parameterised over an arbitrary Rust crate.** Given any
Cargo crate on disk — `cryspen/libcrux-iot`, a user's library, an
upstream test suite — it must produce a per-declaration report saying:
of the *N* function/global/type decls in the crate, how many round-trip
through Aeneas's cert pipeline, how many compile downstream, and how
many are differentially equivalent to a trusted oracle (mainline Aeneas
and/or the developer's source Rust). The four-artifact picture
(R₀/R₁/L₀/L₁) is unchanged; only the input frontier moves outward.

The point is not to add new gates. The point is to stop hand-wiring
each fixture, so that adding a new crate to the audit costs a one-line
config entry, not a day of per-fixture Lean/Rust runner authoring.

## 2. Input Contract

The meta-harness must accept **one** of three input shapes, in
decreasing order of how much the user has to think:

| Shape | What the user provides | What the harness derives |
|---|---|---|
| `--crate <path>` | Path to a Cargo crate root (containing `Cargo.toml`) | Runs Charon (`charon rustc --preset=aeneas`) to produce one `.llbc` per crate; runs `aeneas -emit-cert` and `aeneas -backend lean` from there. |
| `--llbc <path>` | Path to a pre-built `.llbc` file (or a directory of them) | Runs `aeneas -emit-cert` to produce `.cert.json`; reads function/type/global lists from the LLBC. |
| `--cert <path>` | Path to a pre-built `.cert.json` | Skips Charon and OCaml-side passes entirely; uses the cert as the authoritative decl list. Useful for replaying a cert that came from a CI machine the user can't reproduce locally. |

A fourth, optional input is a **manifest file** (`meta-harness.toml`
in the crate root, by convention). The manifest is how the user
expresses things the harness cannot infer: which functions are
non-differential-testable (closures, FFI), which test vectors to use
for which function, and which decls are expected to be skipped at
which gate. The manifest is *the* extension point — everything that
would otherwise be a hardcoded skip-list or per-fixture runner stub
should live there. A minimal manifest is empty (`{}`); the harness
should fall back to inference for everything the manifest doesn't
override. Concrete keys we expect at minimum:

```toml
# meta-harness.toml — all fields optional.

[gates]
# Disable a gate entirely for this crate.
g_rust  = "skip"             # the cert-Rust backend isn't useful for ml-dsa
g_lean  = "auto"             # the default — try to drive everything
g_byte  = "auto"
g_rfl   = "skip"             # gate doesn't exist yet

[decls."crate::module::foo"]
# Per-decl overrides. Path syntax matches Charon's name resolution.
g_rust  = { skip = "takes &dyn Trait" }
g_lean  = { vectors = "vectors/foo.json" }   # user-supplied test inputs

[lean.shim]
# Optional extra Lean imports the generated module needs.
extra_imports = ["MyProject.Shim"]
```

The harness must work without a manifest at all (best-effort
inference); the manifest only ratchets quality up.

## 3. Output Contract

The harness emits one machine-readable report (`report.json`) plus a
human-readable Markdown summary (`report.md`). The JSON is the source
of truth; the Markdown is rendered from it.

Per-decl shape (one entry per Rust `fn` / `const` / `static` /
top-level `struct` / `enum` / `trait` / `impl`):

```json
{
  "crate": "libcrux-sha3",
  "decl_path": "libcrux_sha3::shake128::absorb_block",
  "decl_kind": "fn",
  "charon_ok": true,
  "cert_ok": true,
  "gates": {
    "c_lean_aeneas":  { "status": "pass" },
    "c_lean_ours":    { "status": "pass" },
    "c_rust":         { "status": "pass" },
    "g_byte":         { "status": "divergent", "reason": "wrapping_add shim" },
    "g_rust":         { "status": "pass", "vectors": 64 },
    "g_lean":         { "status": "skip", "reason": "needs &mut [u8] input" },
    "g_rfl":          { "status": "not-run" }
  },
  "evidence": { "diff": "out/.../absorb_block.diff" }
}
```

Aggregate shape (top-level of `report.json`):

```json
{
  "crate":  "libcrux-sha3",
  "decls":  547,
  "compile": { "ours": 412, "aeneas": 547, "rust": 408 },
  "differential": { "byte_pass": 38, "rust_pass": 312, "lean_pass": 287 },
  "skipped":   { "byte": 4, "rust": 121, "lean": 145 },
  "mismatch":  { "byte": 0, "rust": 0, "lean": 2 }
}
```

`status` is one of `pass | divergent | mismatch | skip | not-run |
fail`. `divergent` means "known and listed in the manifest with a
documented reason"; `mismatch` means "unexpected — fail the build."
This is the same distinction `scripts/compare-backends.sh` already
makes for G_byte and which we'd preserve.

## 4. Per-Gate Scope

The honest summary is that **G_byte is fully automatable, G_lean
mostly is, and G_rust requires per-decl test-vector hints for non-trivial
input types.** Per-gate detail:

### G_byte (L₀ vs L₁, byte-identical)

This is the closest to free. `scripts/compare-backends.sh --sweep`
already runs the comparison over every `tests/llbc/*.llbc` in this
repo with zero per-fixture wire-in; the meta-harness generalises that
script's logic to "any directory of `.llbc` files." The only
project-specific knob is the known-divergent allowlist (currently
`scripts/compare-backends-known-divergent.txt`), which should move
into `meta-harness.toml`'s `[decls.*]` table. No per-decl test
inputs, no Lean runners — just `cmp -s`.

### G_rust (R₀ vs R₁, proptest)

Inherently per-decl, because random-testing a function requires (a)
calling the source Rust impl, (b) calling the emitted-Rust model
impl, and (c) feeding both with random inputs of the right type.
The meta-harness can fully automate the first two (a generated `lib.rs`
can `#[path]`-include both sides, the way `tests/lean-checker/differential/`
does today by hand). The third — generating `Arbitrary` instances —
is automatable only for the closed world of primitive scalars,
fixed-size arrays of scalars, and tuples thereof. For everything else
(user ADTs, `&mut`, slices with semantic length constraints, generics)
the manifest must provide a vector source or the decl is skipped.
Output: per-decl proptest pass count + observed input range.

### G_lean (R₀ vs L₁, executed)

The current `tests/lean-checker/lean-diff/` design — per-fixture
hand-written `*Runner.lean` that prints byte-stable
`<fn>(args) = ok <val>` lines, mirrored by `rust-runner/src/main.rs` —
is the right *shape* but the wrong *factoring*. The meta-harness
should generate both sides from a single per-decl spec consisting of
(decl path, list of input vectors, serialiser for the return type).
For decls returning a primitive `Result<T>` where `T` has a `Display`
impl on the Rust side and a `ToString`/`reprPrec` instance on the
Lean side, the generator is mechanical. Where it isn't (ADT returns,
back-closures, &mut roundtrip), the manifest names a custom
serialiser pair, or the decl is skipped. The generated `LeanDiff/Main.lean`
and `rust-runner/src/main.rs` should be derived files, not hand-edited.

### G_rfl (L₀ vs L₁, defeq under `rfl`)

Doesn't exist yet. Its place in the meta-harness is the same as
G_byte's, but where the comparator is a Lean elaborator session
(import both modules under different namespaces, generate
`example : L₀.foo = L₁.foo := by rfl` per decl, collect compile
results). Project-agnostic by construction; the per-decl shape is
just `decl_path` and a yes/no answer. Deferred until after the
implementation pass lands G_byte/G_lean refactors.

### Where automation breaks down (acknowledge)

Some Rust shapes are unreachable for *any* of the executed gates and
should be detected and skip-listed by the harness without manual
intervention:

- `fn(&dyn Trait)` parameters — no canonical random input.
- `fn(impl FnMut(X) -> Y)` parameters — closures aren't `Arbitrary`.
- `async fn` — the cert pipeline doesn't support it; even if it did,
  proptest harnessing would need a runtime.
- Functions whose only side effect is FFI (`extern "C"`).
- Generic functions with no monomorphisation point in the test crate
  (we have no way to pick a `T`).

The harness should detect each of these from the LLBC type and emit
`{ "status": "skip", "reason": "<class>" }` automatically, *not*
require a manifest entry. Manifest entries are for cases inference
gets wrong.

## 5. Per-Decl Granularity

The user's specific ask is "412 of 547 decls compile, 312
differential-pass." This requires the harness to enumerate decls,
not fixtures, as its primary unit. Concretely:

1. **Enumerate.** The LLBC file is the source of truth. After
   `aeneas -emit-cert`, the `.cert.json` carries the full decl list
   (functions, globals, types, traits, trait impls) keyed by Charon's
   stable name path. The harness reads this list once per crate and
   threads decl identity through every gate.
2. **Classify.** For each decl, ask: is it `pub`? Does it have a body
   (vs trait method declaration only)? What's the signature shape?
   Classification answers feed the auto-skip rules in §4.
3. **Run each gate per decl.** G_byte today is per-*file* because
   mainline emits one `.lean` per crate, not per decl. To get
   per-decl granularity we have to either (a) post-process L₀ and L₁
   by parsing both files and matching decls by name (lighter, but
   imprecise on grouping), or (b) drive the comparison decl-by-decl
   by re-invoking `aeneas-check --out` with a `--only-decl <path>`
   filter (heavier, requires a new flag on `aeneas-check`). The right
   answer is probably (a) for now and (b) once the volume justifies
   the flag.
4. **Aggregate.** The aggregate section of `report.json` is just a
   reduction over the per-decl list. The Markdown summary should
   render the aggregate as a table and the per-decl list as a sorted,
   collapsible section.

## 6. What This Replaces

The intent is that, once the meta-harness lands, the following
hand-curated infrastructure goes away or shrinks dramatically:

| Today | After meta-harness |
|---|---|
| `tests/lean-checker/differential/src/lib.rs` (~hundreds of lines of `pub mod <fixture>` blocks mirroring `tests/src/*.rs`) | Deleted. The harness generates an equivalent `lib.rs` at build time from the manifest + auto-classification. |
| `tests/lean-checker/differential/src/model.rs` plus per-fixture `*_model.rs` (e.g. `aggregates_basic_model.rs`, `reborrows_model.rs`) | Deleted. The harness invokes `aeneas-check --rust-model` per decl and uses the output directly. |
| `tests/lean-checker/differential/tests/diff.rs` (per-fixture `proptest!{}` blocks) | Generated. Each block is `(fn name, vector spec)` from the manifest plus the auto-discovered primitive-signature decls. |
| `tests/lean-checker/lean-diff/LeanDiff/*Runner.lean` (per-fixture hand-written Lean drivers) | Generated. One driver per decl, emitted to a fresh `generated/runners/` tree, regenerated on every run. |
| `tests/lean-checker/lean-diff/rust-runner/src/main.rs` (per-fixture hand-written Rust mirror) | Generated, byte-stable with the Lean side, from the shared per-decl spec. |
| `scripts/compare-backends.sh --sweep` plus `scripts/compare-backends-known-divergent.txt` | Stays in spirit but moves under the meta-harness; the allowlist moves into `meta-harness.toml`. |
| `scripts/compare-backends.sh <fixture.rs>` (interactive single-fixture diff) | Kept as a developer convenience; reuses meta-harness libraries under the hood. |

The Lake project skeleton (`tests/lean-checker/lean-diff/lakefile.lean`)
and the cargo project skeleton (`tests/lean-checker/differential/Cargo.toml`)
stay — they're the build sandboxes the generated files live in. What
changes is that nothing in those trees is hand-edited at fixture
granularity any more.

Cost estimate: a careful pass at this is **roughly two engineer-weeks**.
The Rust-side generator (G_rust) and the Lean-side generator (G_lean)
are each about half that; G_byte refactoring is a day; report
formatting and manifest plumbing is the rest. The reason it isn't
faster is that the generators have to handle the per-decl
serialiser-pair invariant (Lean and Rust must print byte-identical
strings for the same value) for the long tail of primitive types,
and getting that exactly right is fiddly.

## 7. What's NOT Automated

Be explicit about the unsupported tail, so the next reader doesn't
chase ghosts:

- **Closures and higher-order fns.** `fn(impl FnMut(X) -> Y)` — no
  `Arbitrary`. The harness skips these and the manifest cannot
  rescue them (you'd have to write a custom Rust driver).
- **`&mut T` round-tripping.** Differential-testing `fn(&mut Foo)`
  requires comparing the post-state of `Foo`, which means a
  `PartialEq` instance and a serialiser pair. Doable for the
  primitive `&mut u32` case; defer for nested `&mut` over ADTs.
- **Generics without a monomorphisation site in the test crate.**
  We have no policy for picking a `T`.
- **`async fn`.** Cert pipeline doesn't support it.
- **FFI / `extern "C"`.** Out of scope for the cert pipeline.
- **Decls that exercise the *interpreter* but not the *emitter*.**
  Some tests in `tests/src/` are present to stress Charon and the
  OCaml-side symbolic interpreter; their emitted Lean is uninteresting.
  The harness still reports compile status; it doesn't try to find a
  differential angle.
- **Trait-method dispatch through `dyn Trait`.** Even where the
  signature is otherwise primitive, the dispatch makes the call
  non-deterministic from the harness's perspective.

The right posture is: the harness reports honest skip counts with a
reason class, and the user can decide whether the skip rate is
acceptable for their crate. We do *not* try to make the skip rate
go to zero; we try to make it well-explained.

## 8. Open Design Questions

These need resolving in the implementation pass, not now:

1. **Charon invocation per crate vs per workspace.** A real Cargo
   workspace has many crates with shared `[dependencies]`. Does the
   harness drive Charon once per leaf crate, or once per workspace
   member? Charon's `--preset=aeneas` flow assumes a single crate;
   workspace support may need upstream work.

2. **Where does the manifest live for crates we don't own?** For
   `libcrux-iot` we can vendor `meta-harness.toml` in the libcrux
   repo. For a user's private project the user owns it. For
   testing-the-tester on `tests/src/*.rs` we'd want it in this repo.
   The harness needs a search-path convention.

3. **Per-decl `--only-decl` flag on `aeneas-check`.** §5 step 3
   sketched two approaches to per-decl G_byte. Approach (b) needs an
   upstream-ish change to `aeneas-check` (and probably `main.exe`).
   Worth the cost? Depends on how often we want decl-grained
   regeneration vs file-grained.

4. **Serialiser-pair invariant.** What's the canonical byte-stable
   format for, say, `(u32, [u8; 4], Option<i32>)`? Today's hand-written
   runners pick ad-hoc formats per fixture. We need one decision
   that covers the primitive-shape closure exactly.

5. **Cross-crate decl identity.** When mainline Aeneas and our
   cert-driven backend disagree on naming (e.g. `impl`-namespace
   prefixing under `-impl-namespace`), per-decl matching by string
   path becomes ambiguous. Probably we lock the harness to one
   naming convention and report any L₀ that doesn't match it as
   `mismatch`.

6. **CI integration.** Two-week meta-harness implementation lands
   the machinery; CI plugging is separate. Question: do we run the
   full sweep on every PR (slow, complete) or only on a labelled
   subset (fast, gappy)? Probably both, controlled by a CI flag.

7. **Backend coverage beyond Lean.** Aeneas emits F\*, Coq, HOL4 too.
   The four-artifact picture in `differential-testing-plan.md` is
   Lean-centric. Should the meta-harness be backend-parametric from
   the start, or Lean-only with a refactor budget later?
