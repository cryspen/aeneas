// HAND-CURATED MODEL FILE for the differential harness.
//
// Each block below is the verbatim `aeneas-check --rust-model` output
// for the named cert, renamed with a `<crate>_<fn>_model` suffix so
// multiple fixtures coexist in a single Rust module. Regenerate with
//
//   aeneas-lean-checker/.lake/build/bin/aeneas-check \
//     tests/llbc/<fixture>.cert.json --rust-model /tmp/<fixture>_m.rs
//
// and reconcile any rename diffs.

// ---- incr_cert.cert.json ----
//   ✓ incr        — `(x1 + 1u32)`
//   ✓ incr_local  — `(x1 + 1u32)`

pub fn incr_model(x1: u32) -> u32 {
    (x1 + 1u32)
}

pub fn incr_local_model(x1: u32) -> u32 {
    (x1 + 1u32)
}

// ---- constants.cert.json ----
//   ✓ incr        — `(x1 + 1u32)`         (same shape as incr_cert::incr)
//   ✓ mk_pair0    — `(x1, x2)`
//   ✓ add         — `(x1 + x2)`           (release-mode wraps for i32)

pub fn constants_incr_model(x1: u32) -> u32 {
    (x1 + 1u32)
}

pub fn constants_mk_pair0_model(x1: u32, x2: u32) -> (u32, u32) {
    (x1, x2)
}

pub fn constants_add_model(x1: i32, x2: i32) -> i32 {
    (x1 + x2)
}

// ---- bitwise.cert.json ----
//   ✓ shift_u32   — `(x1 >> 16usize) << 16usize`
//   ✓ shift_i32   — `(x1 >> 16isize) << 16isize`
//   ✓ xor_u32     — `(x1 ^ x2)`
//   ✓ or_u32      — `(x1 | x2)`
//   ✓ and_u32     — `(x1 & x2)`

pub fn bitwise_shift_u32_model(x1: u32) -> u32 {
    let t0 = (x1 >> 16usize);
    (t0 << 16usize)
}

pub fn bitwise_shift_i32_model(x1: i32) -> i32 {
    let t0 = (x1 >> 16isize);
    (t0 << 16isize)
}

pub fn bitwise_xor_u32_model(x1: u32, x2: u32) -> u32 {
    (x1 ^ x2)
}

pub fn bitwise_or_u32_model(x1: u32, x2: u32) -> u32 {
    (x1 | x2)
}

pub fn bitwise_and_u32_model(x1: u32, x2: u32) -> u32 {
    (x1 & x2)
}

// ---- compare_simple.cert.json ----
//   ✓ id_u32      — identity
//   ✓ add_u32     — `u32::wrapping_add(x1, x2)`   (post-3d086b79 brace fix)

pub fn compare_simple_id_u32_model(x1: u32) -> u32 {
    x1
}

pub fn compare_simple_add_u32_model(x1: u32, x2: u32) -> u32 {
    u32::wrapping_add(x1, x2)
}

// ---- calls.cert.json ----
//   ✓ incr_inner  — `(x1 + 1u32)`              (forward collapses &mut)
//   ✓ pick        — `let t0 = if x1 { x2 } else { x3 }; u32::wrapping_add(t0, 1u32)`

pub fn calls_incr_inner_model(x1: u32) -> u32 {
    (x1 + 1u32)
}

pub fn calls_pick_model(x1: bool, x2: u32, x3: u32) -> u32 {
    let t0 = if x1 { x2 } else { x3 };
    u32::wrapping_add(t0, 1u32)
}

// ---- scalars.cert.json (Phase 4b — new fixture) ----
//   The cert emits ~22 fns; we wire only those whose body is a clean
//   self-contained arithmetic / bitwise / shift / rotate. The rest
//   (casts that the emitter renders as identity, `Default::default`
//   that gets emitted as `u32::default` without parens, the match-
//   shaped fns that fold to constants) are skipped per the prompt's
//   "well-emitted bodies only" rule. Bodies copied verbatim from
//   /tmp/sweep-rust-models/scalars.rs (post Phase 4a-2 brace fix).

pub fn scalars_u32_use_wrapping_add_model(x1: u32, x2: u32) -> u32 {
    u32::wrapping_add(x1, x2)
}

pub fn scalars_i32_use_wrapping_add_model(x1: i32, x2: i32) -> i32 {
    i32::wrapping_add(x1, x2)
}

pub fn scalars_u32_use_wrapping_sub_model(x1: u32, x2: u32) -> u32 {
    u32::wrapping_sub(x1, x2)
}

pub fn scalars_i32_use_wrapping_sub_model(x1: i32, x2: i32) -> i32 {
    i32::wrapping_sub(x1, x2)
}

pub fn scalars_u32_use_shift_right_model(x1: u32) -> u32 {
    (x1 >> 2i32)
}

pub fn scalars_i32_use_shift_right_model(x1: i32) -> i32 {
    (x1 >> 2i32)
}

pub fn scalars_u32_use_shift_left_model(x1: u32) -> u32 {
    (x1 << 2i32)
}

pub fn scalars_i32_use_shift_left_model(x1: i32) -> i32 {
    (x1 << 2i32)
}

pub fn scalars_add_and_model(x1: u32, x2: u32) -> u32 {
    let t0 = (x2 & x1);
    let t1 = (x2 & x1);
    (t0 + t1)
}

pub fn scalars_u32_use_rotate_right_model(x1: u32) -> u32 {
    u32::rotate_right(x1, 2u32)
}

pub fn scalars_i32_use_rotate_right_model(x1: i32) -> i32 {
    i32::rotate_right(x1, 2u32)
}

pub fn scalars_u32_use_rotate_left_model(x1: u32) -> u32 {
    u32::rotate_left(x1, 2u32)
}

pub fn scalars_i32_use_rotate_left_model(x1: i32) -> i32 {
    i32::rotate_left(x1, 2u32)
}

// ---- demo.cert.json (Phase 4b — new fixture) ----
//   `mul2_add1` and `incr` are self-contained (no intra-crate calls).
//   `use_mul2_add1` and `use_incr` reference `demo::*` in the emit —
//   would need module wrapping; skipped. Closure-based `choose` /
//   `list_nth` skipped (M12.2a placeholder).

pub fn demo_mul2_add1_model(x1: u32) -> u32 {
    let t0 = (x1 + x1);
    (t0 + 1u32)
}

pub fn demo_incr_model(x1: u32) -> u32 {
    (x1 + 1u32)
}
