//! Rust oracle for the Lean differential harness.
//!
//! Produces byte-identical lines to those `LeanDiff/Main.lean` prints,
//! mirroring the semantics of the source `tests/src/<fixture>.rs`
//! functions. A `diff` between the two streams verifies that the
//! Lean code emitted by `aeneas-check` from `<fixture>.cert.json`
//! computes the same thing as the original Rust.
//!
//! Caveat about overflow semantics:
//!   The `RuntimeShim/Aeneas/Std.lean` `(+)` instance on `Std.U32` is
//!   defined as `liftRes2 UInt32.add`, i.e. it wraps and returns
//!   `Result.ok`. The real Aeneas runtime returns `Result.error
//!   .overflow` instead. So this oracle uses `wrapping_add` and
//!   always prints `ok …`, matching the shim. The test is therefore
//!   a *correct-against-the-shim* differential — it validates that
//!   the cert -> Lean emitter preserves semantics MODULO the shim's
//!   chosen overflow convention. The next agent could lift this
//!   restriction by linking against the full `backends/lean/`
//!   runtime once the mathlib-cold-build cost is acceptable.

// ---------------------------------------------------------------------------
// Source Rust functions (copies of the `tests/src/` definitions)
// ---------------------------------------------------------------------------

mod incr_cert {
    pub fn incr(x: u32) -> u32 {
        x.wrapping_add(1)
    }
    pub fn incr_local(y: u32) -> u32 {
        // tests/src/incr_cert.rs: `let r = &mut y; *r += 1; y`.
        y.wrapping_add(1)
    }
}

mod compare_simple {
    pub fn id_u32(x: u32) -> u32 {
        x
    }
    pub fn incr_val(x: u32) -> u32 {
        x.wrapping_add(1)
    }
    pub fn add_u32(a: u32, b: u32) -> u32 {
        a.wrapping_add(b)
    }
}

mod calls {
    pub fn incr_inner(y: u32) -> u32 {
        y.wrapping_add(1)
    }
    pub fn incr_via_helper(x: u32) -> u32 {
        incr_inner(x)
    }
    pub fn pick(b: bool, x: u32, y: u32) -> u32 {
        let r = if b { x } else { y };
        r.wrapping_add(1)
    }
}

// ---------------------------------------------------------------------------
// Line formatting — must match `LeanDiff/Common.lean::mkLine` exactly.
// ---------------------------------------------------------------------------

fn ok_u32(fixture: &str, fn_name: &str, args: &[String], v: u32) {
    println!("{}::{}({}) = ok {}", fixture, fn_name, args.join(","), v);
}

// ---------------------------------------------------------------------------
// Test vectors — must match the per-fixture runner's vectors in order.
// ---------------------------------------------------------------------------

const INCR_U32: [u32; 8] = [
    0,
    1,
    2,
    41,
    0xFFFFFFFE,
    0xFFFFFFFF,
    0x7FFFFFFF,
    0x80000000,
];

const COMPARE_U32: [u32; 8] = [
    0,
    1,
    2,
    42,
    0xFFFFFFFE,
    0xFFFFFFFF,
    0x80000000,
    0x7FFFFFFF,
];

const COMPARE_PAIRS: &[(u32, u32)] = &[
    (0, 0),
    (1, 2),
    (0xFFFFFFFF, 1),
    (0xFFFFFFFE, 1),
    (0xFFFFFFFF, 0xFFFFFFFF),
    (0x80000000, 0x80000000),
];

const CALLS_U32: [u32; 7] = [0, 1, 41, 42, 99, 0xFFFFFFFE, 0xFFFFFFFF];

const PICK_TRIPLES: &[(bool, u32, u32)] = &[
    (true, 0, 99),
    (false, 0, 99),
    (true, 42, 7),
    (false, 42, 7),
    (true, 0xFFFFFFFF, 0),
    (false, 0xFFFFFFFF, 0),
    (true, 0, 0xFFFFFFFF),
    (false, 0, 0xFFFFFFFF),
];

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    // incr_cert
    for &x in &INCR_U32 {
        ok_u32("incr_cert", "incr", &[x.to_string()], incr_cert::incr(x));
    }
    for &x in &INCR_U32 {
        ok_u32(
            "incr_cert",
            "incr_local",
            &[x.to_string()],
            incr_cert::incr_local(x),
        );
    }

    // compare_simple
    for &x in &COMPARE_U32 {
        ok_u32(
            "compare_simple",
            "id_u32",
            &[x.to_string()],
            compare_simple::id_u32(x),
        );
    }
    for &x in &COMPARE_U32 {
        ok_u32(
            "compare_simple",
            "incr_val",
            &[x.to_string()],
            compare_simple::incr_val(x),
        );
    }
    for &(a, b) in COMPARE_PAIRS {
        ok_u32(
            "compare_simple",
            "add_u32",
            &[a.to_string(), b.to_string()],
            compare_simple::add_u32(a, b),
        );
    }

    // calls
    for &x in &CALLS_U32 {
        ok_u32(
            "calls",
            "incr_inner",
            &[x.to_string()],
            calls::incr_inner(x),
        );
    }
    for &x in &CALLS_U32 {
        ok_u32(
            "calls",
            "incr_via_helper",
            &[x.to_string()],
            calls::incr_via_helper(x),
        );
    }
    for &(b, x, y) in PICK_TRIPLES {
        ok_u32(
            "calls",
            "pick",
            &[b.to_string(), x.to_string(), y.to_string()],
            calls::pick(b, x, y),
        );
    }
}
