# `translation.json` produced by `-emit-json`

When Aeneas is invoked with `-emit-json` (Lean backend only) it writes a `translation.json` file alongside the generated Lean files.

## Purpose

The manifest describes **what Aeneas did**: the Lean declarations it produced and their connection to the original Rust source. Most fields record data that exists only after translation and is not present in the `.llbc` input. Consumers can join the two artefacts via `def_id` to obtain the full data.

## Location

`translation.json` is written to the top-level output directory passed via `-dest`. 

## Schema

```json
{
  "aeneas_version": "abc1234",
  "charon_version": "xyz5678",
  "crate": "my_crate",
  "functions": [...],
  "types": [...],
  "globals": [...],
  "trait_decls": [...],
  "trait_impls": [...]
}
```

### Function entries

| Field | Always present | Meaning |
|---|---|---|
| `def_id` | yes | `FunDeclId` (join key into `.llbc`) |
| `lean_name` | yes | Full Lean name (`Namespace.Name`) |
| `extract_name` | yes | The same string, under the name `-external-names` reads |
| `lean_file` | yes | The Lean file this is in, relative to translate.json |
| `rust_name` | yes | Full Rust name |
| `rust_pattern` | yes | `rust_name` in name-pattern syntax (see "Reading the manifest back") |
| `is_local` | yes | `true` if defined in the current crate, `false` if external |
| `source` | yes | Rust source location: `{ "file": "...", "begin_line": N, "end_line": M }` |
| `is_opaque` | yes | Extracted as an axiom |
| `can_fail` | yes | Return type wrapped in `Result` (function can panic) |
| `can_diverge` | yes | May not terminate |
| `is_rec` | yes | Part of a mutually recursive group |
| `reducible` | yes | Marked as reducible by Aeneas |
| `loop` | loop entries only | `{ "id": N, "pos": [...], "is_body": bool }` |
| `parent_lean_name` | loop entries only | `lean_name` of the enclosing Rust function |

`loop` and `parent_lean_name` appear together or not at all.

**Loop position** (`loop.pos`): nesting path of the loop in the source function. `[0]` is the first top-level loop, `[0, 1]` is the second loop nested inside it, etc. Matches `Pure.fun_decl.loop_pos`.

**One Rust function, many entries**: a function with several loops produces multiple entries all sharing the same `def_id`.

### Type and global entries

Type and global entries carry `def_id`, `lean_name`, `extract_name`, `lean_file`, `rust_name`, `rust_pattern`, `is_local`, and `source`; global entries additionally carry `can_fail`. Note that `def_id` is `TypeDeclId` or `GlobalDeclId` respectively. 

### Trait entries

`trait_decls` entries carry the same standard fields as type entries: `def_id` (a `TraitDeclId`), `lean_name`, `extract_name`, `lean_file`, `rust_name`, `rust_pattern`, `is_local`, and `source`. Builtin traits are not included in the outputted json.

`trait_impls` entries carry the same standard fields (`def_id` is a `TraitImplId`) plus a link to the trait they implement:

| Field | Meaning |
|---|---|
| `impl_trait_def_id` | `TraitDeclId` of the implemented trait. |
| `impl_trait_rust_name` | Full Rust path of the implemented trait. |
| `impl_trait_is_builtin` | `true` when the implemented trait is builtin. |

**Note:** `impl_trait_def_id` is always a valid LLBC trait decl. However it has a matching entry in this manifest's `trait_decls` for local traits but not for builtin traits. Equivalently, `impl_trait_is_builtin` iff there is no entry for `impl_trait_def_id` in this manifest's `trait_decls`.

## Reading the manifest back

A `translation.json` written for one crate can be passed to `-external-names` when
translating a crate which depends on it, so that the second crate's references to the
first resolve to its Lean names instead of becoming axioms of its own. No conversion step
is needed. `tests/src/roundtrip-lib` and `tests/src/roundtrip-user` are a worked example.

**`extract_name`** repeats `lean_name` under the name a backend-agnostic reader asks
for; `lean_name` says which backend produced it. **`rust_pattern`** is the pattern the
entry
is registered under, which is *not* always the pattern form of `rust_name`: the latter is
human-readable and stops being pattern syntax once an impl block is involved
(`m::{impl m::Trait for bool}::f` against `m::{m::Trait<bool>}::f`), and on `trait_impls`
the two describe different things, since an implementation is looked up under the trait it
implements applied to its arguments (`m::Trait<m::Ty>`) rather than under its own path.

Two cases the reader cannot resolve:

- **A crate translated for several targets at once** (`--targets a,b`) has per-target
  definitions sharing a Rust path, while the pattern syntax has no way to name a target,
  so their rows collapse onto one pattern. A pattern may be mapped only once, so the file
  is refused rather than one architecture's definition silently chosen.
- **Some names have no pattern.** The name matcher prints patterns it cannot read back:
  const generics parse at one digit but not two, and a disambiguator works on a named
  element but not the anonymous one (`closure#1` against `_#1`). Such an entry is skipped
  with a warning; the rest of the manifest is used.

A `functions` row with a `loop` key is skipped too — it describes a generated loop
declaration under the enclosing function's name, not a definition Rust can call.
