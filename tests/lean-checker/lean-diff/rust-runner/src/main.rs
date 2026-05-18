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

mod bitwise {
    // Mirrors tests/src/bitwise.rs. The Lean shim's shift instances
    // are `liftRes2 UInt32.shiftLeft` / `Int32.shiftLeft`, which on
    // Lean's side perform a 32-bit wrapping shift; the Rust source
    // uses `>>` / `<<` which would panic on overflow. We use
    // `wrapping_shr` / `wrapping_shl` so the oracle matches the
    // shim's panic-free behavior on the cross-language vectors.
    pub fn shift_u32(a: u32) -> u32 {
        let i: u32 = 16;
        let t = a.wrapping_shr(i);
        t.wrapping_shl(i)
    }
    pub fn shift_i32(a: i32) -> i32 {
        let i: u32 = 16;
        let t = a.wrapping_shr(i);
        t.wrapping_shl(i)
    }
    pub fn xor_u32(a: u32, b: u32) -> u32 { a ^ b }
    pub fn or_u32(a: u32, b: u32) -> u32 { a | b }
    pub fn and_u32(a: u32, b: u32) -> u32 { a & b }
}

mod scalars {
    // Mirrors the differential-testable subset of tests/src/scalars.rs.
    // The skipped fns (casts, defaults, `_use_bits`, `match_*`) are
    // documented in the Lean-side ScalarsRunner doc comment.
    pub fn u32_use_wrapping_add(x: u32, y: u32) -> u32 { x.wrapping_add(y) }
    pub fn i32_use_wrapping_add(x: i32, y: i32) -> i32 { x.wrapping_add(y) }
    pub fn u32_use_wrapping_sub(x: u32, y: u32) -> u32 { x.wrapping_sub(y) }
    pub fn i32_use_wrapping_sub(x: i32, y: i32) -> i32 { x.wrapping_sub(y) }

    // The shim's shift instances use `wrapping_shr` / `wrapping_shl`
    // semantics (same as bitwise.rs). The source `>> 2` / `<< 2`
    // never panics on these inputs (rhs is a constant 2), so the
    // wrapping vs panicking choice doesn't matter here, but we use
    // wrapping_* for consistency.
    pub fn u32_use_shift_right(x: u32) -> u32 { x.wrapping_shr(2) }
    pub fn i32_use_shift_right(x: i32) -> i32 { x.wrapping_shr(2) }
    pub fn u32_use_shift_left(x: u32) -> u32 { x.wrapping_shl(2) }
    pub fn i32_use_shift_left(x: i32) -> i32 { x.wrapping_shl(2) }

    pub fn add_and(a: u32, b: u32) -> u32 {
        (b & a).wrapping_add(b & a)
    }

    pub fn u32_use_rotate_right(x: u32) -> u32 { x.rotate_right(2) }
    pub fn i32_use_rotate_right(x: i32) -> i32 { x.rotate_right(2) }
    pub fn u32_use_rotate_left(x: u32) -> u32 { x.rotate_left(2) }
    pub fn i32_use_rotate_left(x: i32) -> i32 { x.rotate_left(2) }
}

mod demo {
    // Session 5 (Item 2): mirrors the well-emitted subset of
    // tests/src/demo.rs. The skipped decls (Counter trait + impl,
    // list_nth*, choose, i32_id) are documented in
    // `LeanDiff/DemoRunner.lean`.
    pub fn mul2_add1(x: u32) -> u32 {
        x.wrapping_add(x).wrapping_add(1)
    }
    pub fn use_mul2_add1(x: u32, y: u32) -> u32 {
        mul2_add1(x).wrapping_add(y)
    }
    pub fn incr(x: u32) -> u32 {
        x.wrapping_add(1)
    }
    pub fn use_incr() {
        let _ = incr(0);
        let _ = incr(0);
        let _ = incr(0);
    }
    // Aeneas modular-add: `(x + y) - 3329` then mask via `>> 16i32`.
    // The shim renders `>>` as a wrapping shift; we mirror with
    // `wrapping_shr`. The `wrapping_sub(x + y, 3329)` produces the
    // 2-complement of the diff when underflow occurs; the high bits
    // turn 0xFFFF_FFFF when negative, 0x0000_0000 when non-negative.
    // Masking with 3329 gives 3329 (to add back) or 0 (to keep).
    pub fn mod_add(x: u32, y: u32) -> u32 {
        let t2 = x.wrapping_add(y);
        let t3 = t2.wrapping_sub(3329);
        // shim emit: `(t3 >>> 16#i32)` — `>>>` is `core.num.U32.shiftRight`
        // (wrapping); the rhs is u32. `wrapping_shr` matches.
        let t4 = t3.wrapping_shr(16);
        let t5 = 3329u32 & t4;
        t3.wrapping_add(t5)
    }
}

mod paper {
    // Session 7 (Item 3): mirrors the well-emitted subset of
    // tests/src/paper.rs. Only `ref_incr` is wired in — the rest of
    // paper hits emit gaps documented in
    // `LeanDiff/PaperRunner.lean`.
    pub fn ref_incr(x: i32) -> i32 {
        x.wrapping_add(1)
    }
}

mod constants {
    // Mirrors the subset of tests/src/constants.rs that the
    // ConstantsRunner exercises. Only the scalar-returning + tuple
    // functions and the nullary const/static initialisers whose Lean
    // emit is non-placeholder. Session 5 Item 1 added X1, Q2, Q3,
    // S2, get_z1, get_z2, unwrap_y, YVAL.
    pub const fn incr(n: u32) -> u32 {
        n.wrapping_add(1)
    }
    pub const fn add(a: i32, b: i32) -> i32 {
        a.wrapping_add(b)
    }
    pub const fn mk_pair0(x: u32, y: u32) -> (u32, u32) {
        (x, y)
    }
    pub struct Wrap<T> {
        pub value: T,
    }
    impl<T> Wrap<T> {
        pub const fn new(value: T) -> Wrap<T> {
            Wrap { value }
        }
    }
    pub const fn unwrap_y() -> i32 {
        Y.value
    }
    pub const fn get_z1() -> i32 {
        const Z1: i32 = 3;
        Z1
    }
    pub const fn get_z2() -> i32 {
        add(Q1, add(get_z1(), Q3))
    }
    pub const X0: u32 = 0;
    pub const X1: u32 = u32::MAX;
    pub const X2: u32 = 3;
    pub const X3: u32 = incr(32);
    pub const Y: Wrap<i32> = Wrap::new(2);
    pub const YVAL: i32 = unwrap_y();
    pub const Q1: i32 = 5;
    pub const Q2: i32 = Q1;
    pub const Q3: i32 = add(Q2, 3);
    pub const P0: (u32, u32) = mk_pair0(0, 1);
    pub const P2: (u32, u32) = (0, 1);
    pub static S1: u32 = 6;
    pub static S2: u32 = incr(S1);
}

// ---------------------------------------------------------------------------
// Line formatting — must match `LeanDiff/Common.lean::mkLine` exactly.
// ---------------------------------------------------------------------------

fn ok_u32(fixture: &str, fn_name: &str, args: &[String], v: u32) {
    println!("{}::{}({}) = ok {}", fixture, fn_name, args.join(","), v);
}

fn ok_i32(fixture: &str, fn_name: &str, args: &[String], v: i32) {
    // The Lean side's `Show1 Int32` instance prints the signed decimal
    // via `Int32.toInt`; match that here with Rust's signed `Display`.
    println!("{}::{}({}) = ok {}", fixture, fn_name, args.join(","), v);
}

fn ok_tuple_u32(fixture: &str, fn_name: &str, args: &[String], v: (u32, u32)) {
    println!(
        "{}::{}({}) = ok {},{}",
        fixture,
        fn_name,
        args.join(","),
        v.0,
        v.1
    );
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

// Constants fixture vectors. Must agree with
// `LeanDiff/ConstantsRunner.lean` order.
const CONSTANTS_U32: [u32; 9] = [
    0,
    1,
    2,
    41,
    100,
    0xFFFFFFFE,
    0xFFFFFFFF,
    0x7FFFFFFF,
    0x80000000,
];

const CONSTANTS_ADD_I32: &[(i32, i32)] = &[
    (0, 0),
    (1, 1),
    (1, -1),
    (-1, 1),
    (0x7FFFFFFF, 1),
    (-0x80000000, -1),
    (100, 200),
    (-100, -200),
];

const CONSTANTS_MK_PAIR_U32: &[(u32, u32)] = &[
    (0, 0),
    (1, 2),
    (42, 7),
    (0xFFFFFFFF, 1),
    (0x7FFFFFFF, 0x80000000),
];

// Bitwise fixture vectors. Must agree with
// `LeanDiff/BitwiseRunner.lean` order.
const BITWISE_U32: [u32; 6] = [
    0,
    1,
    0xDEADBEEF,
    0xFFFFFFFF,
    0x80000000,
    0x7FFFFFFF,
];

const BITWISE_I32: [i32; 6] = [
    0,
    1,
    -1,
    0x7FFFFFFF,
    -0x80000000,
    0xDEADBEEFu32 as i32,
];

const BITWISE_PAIRS_U32: &[(u32, u32)] = &[
    (0, 0),
    (0xFFFFFFFF, 0),
    (0xFFFFFFFF, 0xFFFFFFFF),
    (0xDEADBEEF, 0xCAFEBABE),
    (0x55555555, 0xAAAAAAAA),
    (0x12345678, 0x87654321),
];

// Scalars fixture vectors. Must agree with ScalarsRunner.lean.
const SCALARS_U32: [u32; 9] = [
    0,
    1,
    2,
    41,
    0xDEADBEEF,
    0xFFFFFFFE,
    0xFFFFFFFF,
    0x7FFFFFFF,
    0x80000000,
];

const SCALARS_I32: [i32; 8] = [
    0,
    1,
    -1,
    42,
    -42,
    0x7FFFFFFF,
    -0x80000000,
    0xDEADBEEFu32 as i32,
];

const SCALARS_PAIRS_U32: &[(u32, u32)] = &[
    (0, 0),
    (1, 2),
    (0xFFFFFFFF, 1),
    (0xFFFFFFFE, 1),
    (0xFFFFFFFF, 0xFFFFFFFF),
    (0x80000000, 0x80000000),
    (0xDEADBEEF, 0xCAFEBABE),
];

const SCALARS_PAIRS_I32: &[(i32, i32)] = &[
    (0, 0),
    (1, 1),
    (1, -1),
    (-1, 1),
    (0x7FFFFFFF, 1),
    (-0x80000000, -1),
    (100, 200),
    (-100, -200),
];

// Session 5 (Item 2): demo fixture vectors. Must agree with
// `LeanDiff/DemoRunner.lean` order.
const DEMO_U32: [u32; 9] = [
    0,
    1,
    2,
    41,
    0xDEADBEEF,
    0xFFFFFFFE,
    0xFFFFFFFF,
    0x7FFFFFFF,
    0x80000000,
];

const DEMO_PAIRS_U32: &[(u32, u32)] = &[
    (0, 0),
    (1, 2),
    (42, 7),
    (0xFFFFFFFF, 1),
    (0x7FFFFFFF, 0x80000000),
    (1000, 2329),
    (3328, 1),
    (3329, 3329),
];

// Session 7 (Item 3): paper fixture vectors. Must agree with
// `LeanDiff/PaperRunner.lean` order.
const PAPER_I32: [i32; 8] = [
    0,
    1,
    -1,
    41,
    0x7FFFFFFE,
    0x7FFFFFFF,
    -0x80000000,
    -1,
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

    // bitwise
    for &x in &BITWISE_U32 {
        ok_u32(
            "bitwise",
            "shift_u32",
            &[x.to_string()],
            bitwise::shift_u32(x),
        );
    }
    for &x in &BITWISE_I32 {
        ok_i32(
            "bitwise",
            "shift_i32",
            &[x.to_string()],
            bitwise::shift_i32(x),
        );
    }
    for &(a, b) in BITWISE_PAIRS_U32 {
        ok_u32(
            "bitwise",
            "xor_u32",
            &[a.to_string(), b.to_string()],
            bitwise::xor_u32(a, b),
        );
    }
    for &(a, b) in BITWISE_PAIRS_U32 {
        ok_u32(
            "bitwise",
            "or_u32",
            &[a.to_string(), b.to_string()],
            bitwise::or_u32(a, b),
        );
    }
    for &(a, b) in BITWISE_PAIRS_U32 {
        ok_u32(
            "bitwise",
            "and_u32",
            &[a.to_string(), b.to_string()],
            bitwise::and_u32(a, b),
        );
    }

    // constants
    for &x in &CONSTANTS_U32 {
        ok_u32(
            "constants",
            "incr",
            &[x.to_string()],
            constants::incr(x),
        );
    }
    for &(a, b) in CONSTANTS_ADD_I32 {
        ok_i32(
            "constants",
            "add",
            &[a.to_string(), b.to_string()],
            constants::add(a, b),
        );
    }
    for &(x, y) in CONSTANTS_MK_PAIR_U32 {
        ok_tuple_u32(
            "constants",
            "mk_pair0",
            &[x.to_string(), y.to_string()],
            constants::mk_pair0(x, y),
        );
    }
    ok_u32("constants", "X0", &[], constants::X0);
    ok_u32("constants", "X2", &[], constants::X2);
    ok_u32("constants", "X3", &[], constants::X3);
    ok_u32("constants", "S1", &[], constants::S1);
    ok_i32("constants", "Q1", &[], constants::Q1);
    ok_tuple_u32("constants", "P0", &[], constants::P0);
    ok_tuple_u32("constants", "P2", &[], constants::P2);
    // Session 5 (Item 1): the cert walker now recovers the source
    // global through Charon's pre-pass-inserted borrow chain. The
    // previously-skipped const/static initialisers below are wired
    // in here against the Rust-source reference values.
    ok_u32("constants", "X1", &[], constants::X1);
    ok_i32("constants", "Q2", &[], constants::Q2);
    ok_i32("constants", "Q3", &[], constants::Q3);
    ok_u32("constants", "S2", &[], constants::S2);
    ok_i32("constants", "get_z1", &[], constants::get_z1());
    ok_i32("constants", "get_z2", &[], constants::get_z2());
    ok_i32("constants", "unwrap_y", &[], constants::unwrap_y());
    ok_i32("constants", "YVAL", &[], constants::YVAL);

    // scalars
    for &(a, b) in SCALARS_PAIRS_U32 {
        ok_u32("scalars", "u32_use_wrapping_add",
            &[a.to_string(), b.to_string()],
            scalars::u32_use_wrapping_add(a, b));
    }
    for &(a, b) in SCALARS_PAIRS_I32 {
        ok_i32("scalars", "i32_use_wrapping_add",
            &[a.to_string(), b.to_string()],
            scalars::i32_use_wrapping_add(a, b));
    }
    for &(a, b) in SCALARS_PAIRS_U32 {
        ok_u32("scalars", "u32_use_wrapping_sub",
            &[a.to_string(), b.to_string()],
            scalars::u32_use_wrapping_sub(a, b));
    }
    for &(a, b) in SCALARS_PAIRS_I32 {
        ok_i32("scalars", "i32_use_wrapping_sub",
            &[a.to_string(), b.to_string()],
            scalars::i32_use_wrapping_sub(a, b));
    }
    for &x in &SCALARS_U32 {
        ok_u32("scalars", "u32_use_shift_right", &[x.to_string()],
            scalars::u32_use_shift_right(x));
    }
    for &x in &SCALARS_I32 {
        ok_i32("scalars", "i32_use_shift_right", &[x.to_string()],
            scalars::i32_use_shift_right(x));
    }
    for &x in &SCALARS_U32 {
        ok_u32("scalars", "u32_use_shift_left", &[x.to_string()],
            scalars::u32_use_shift_left(x));
    }
    for &x in &SCALARS_I32 {
        ok_i32("scalars", "i32_use_shift_left", &[x.to_string()],
            scalars::i32_use_shift_left(x));
    }
    for &(a, b) in SCALARS_PAIRS_U32 {
        ok_u32("scalars", "add_and",
            &[a.to_string(), b.to_string()],
            scalars::add_and(a, b));
    }
    for &x in &SCALARS_U32 {
        ok_u32("scalars", "u32_use_rotate_right", &[x.to_string()],
            scalars::u32_use_rotate_right(x));
    }
    for &x in &SCALARS_I32 {
        ok_i32("scalars", "i32_use_rotate_right", &[x.to_string()],
            scalars::i32_use_rotate_right(x));
    }
    for &x in &SCALARS_U32 {
        ok_u32("scalars", "u32_use_rotate_left", &[x.to_string()],
            scalars::u32_use_rotate_left(x));
    }
    for &x in &SCALARS_I32 {
        ok_i32("scalars", "i32_use_rotate_left", &[x.to_string()],
            scalars::i32_use_rotate_left(x));
    }

    // demo (Session 5 Item 2)
    for &x in &DEMO_U32 {
        ok_u32("demo", "mul2_add1", &[x.to_string()],
            demo::mul2_add1(x));
    }
    for &(a, b) in DEMO_PAIRS_U32 {
        ok_u32("demo", "use_mul2_add1", &[a.to_string(), b.to_string()],
            demo::use_mul2_add1(a, b));
    }
    for &x in &DEMO_U32 {
        ok_u32("demo", "incr", &[x.to_string()],
            demo::incr(x));
    }
    demo::use_incr();
    println!("demo::use_incr() = ok ()");
    for &(a, b) in DEMO_PAIRS_U32 {
        ok_u32("demo", "mod_add", &[a.to_string(), b.to_string()],
            demo::mod_add(a, b));
    }

    // paper (Session 7 Item 3)
    for &x in &PAPER_I32 {
        ok_i32("paper", "ref_incr", &[x.to_string()], paper::ref_incr(x));
    }
}
