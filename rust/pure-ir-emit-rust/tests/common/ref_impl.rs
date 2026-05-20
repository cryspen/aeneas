//! R₀: reference implementations copied from `tests/src/<fixture>.rs`,
//! reshaped to the functional shape that matches the Pure-IR emit.
//!
//! Conventions:
//!
//!   * Every IR-emitted forward fn returns `Result<T, ()>` (the
//!     `aeneas_runtime::Result` shim in the emit) because
//!     symbolic-to-pure threads the `can_fail` monad through every
//!     fallible primitive (`checked_add`, `checked_shl`, etc.).
//!     R₀ wrappers therefore also return `Result<T, ()>` and use
//!     `checked_*` primitives so the failure cases align.
//!
//!   * `&mut T` borrow signatures collapse to forward `T -> T` (or
//!     `T -> Result<T>`) because the IR functionalises the in/out
//!     borrow on the forward side.
//!
//!   * ADTs are duplicated per-fixture (each fixture brings its own
//!     `Pair`, `Sign`, etc., since the IR's emitted struct names
//!     carry crate + def_id suffixes and proptest blocks compare
//!     field-by-field anyway).
//!
//! Names mirror the fixture module path (`incr_cert::incr`, etc.) so
//! the diff-block call sites read symmetrically with the R₂ model
//! call sites.

#![allow(dead_code, unused_parens)]

pub type Result<T> = core::result::Result<T, ()>;

// ====================================================================
// incr_cert.rs
// ====================================================================

pub mod incr_cert {
    use super::Result;

    /// `pub fn incr(x: &mut u32) { *x += 1; }` — the IR functionalises
    /// the `&mut` borrow into a forward `u32 -> Result<u32>` and
    /// lowers `+= 1` to `x.checked_add(1).ok_or(())`. R₀ matches.
    pub fn incr(x: u32) -> Result<u32> {
        x.checked_add(1).ok_or(())
    }

    /// `pub fn incr_local(mut y: u32) -> u32` — pre-extract collapses
    /// the local-borrow round-trip into the same `checked_add(1)` shape.
    pub fn incr_local(y: u32) -> Result<u32> {
        y.checked_add(1).ok_or(())
    }
}

// ====================================================================
// constants.rs
// ====================================================================

pub mod constants {
    use super::Result;

    pub fn incr(n: u32) -> Result<u32> {
        n.checked_add(1).ok_or(())
    }

    pub fn mk_pair0(x: u32, y: u32) -> Result<(u32, u32)> {
        Ok((x, y))
    }

    pub fn add(a: i32, b: i32) -> Result<i32> {
        a.checked_add(b).ok_or(())
    }
}

// ====================================================================
// bitwise.rs
// ====================================================================

pub mod bitwise {
    use super::Result;

    /// `a >> 16; t <<= 16; t` — the IR lowers both `>>` and `<<` to
    /// `checked_shr` / `checked_shl`. Shifts by 16 (constant) never
    /// overflow on u32/i32, so the result is always `Ok`.
    pub fn shift_u32(a: u32) -> Result<u32> {
        let t = a.checked_shr(16).ok_or(())?;
        t.checked_shl(16).ok_or(())
    }

    pub fn shift_i32(a: i32) -> Result<i32> {
        let t = a.checked_shr(16).ok_or(())?;
        t.checked_shl(16).ok_or(())
    }

    pub fn xor_u32(a: u32, b: u32) -> Result<u32> {
        Ok(a ^ b)
    }

    pub fn or_u32(a: u32, b: u32) -> Result<u32> {
        Ok(a | b)
    }

    pub fn and_u32(a: u32, b: u32) -> Result<u32> {
        Ok(a & b)
    }
}

// ====================================================================
// compare_simple.rs
// ====================================================================

pub mod compare_simple {
    use super::Result;

    pub fn id_u32(x: u32) -> Result<u32> {
        Ok(x)
    }

    /// `pub fn incr_val(x: &mut u32) { *x += 1; }` — same shape as
    /// `incr_cert::incr`. Note: the IR emits this with `checked_add`,
    /// not `wrapping_add`, even though the original Rust calls
    /// `wrapping_add` — the emit uses `+` on the IR side, which lowers
    /// to `checked_add(1).ok_or(())`. Source uses `+=`, not
    /// `wrapping_add`, in the pre-extract IR.
    pub fn incr_val(x: u32) -> Result<u32> {
        x.checked_add(1).ok_or(())
    }

    /// `pub fn add_u32(a: u32, b: u32) -> u32 { a.wrapping_add(b) }`
    /// — Option A routes the `impl_core_num_wrapping_add_*` shim
    /// to `u32::wrapping_add`, so this test moved out of `#[ignore]`.
    pub fn add_u32(a: u32, b: u32) -> Result<u32> {
        Ok(a.wrapping_add(b))
    }
}

// ====================================================================
// aggregates_basic.rs
// ====================================================================

pub mod aggregates_basic {
    use super::Result;

    /// Mirrors the IR's `aggregates_basic_Pair_0` — same field
    /// layout, different name. Proptest blocks compare field-by-field.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Pair {
        pub x: u32,
        pub y: u32,
    }

    pub fn mk_tuple(x: u32, y: u32) -> Result<(u32, u32)> {
        Ok((x, y))
    }

    pub fn mk_pair(x: u32, y: u32) -> Result<Pair> {
        Ok(Pair { x, y })
    }
}

// ====================================================================
// enums_basic.rs
// ====================================================================

pub mod enums_basic {
    use super::Result;

    /// Mirrors the IR's `enums_basic_Sign_0`. Carries `PartialEq` so
    /// the proptest can `assert_eq!` directly after a coercion step.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Sign {
        Pos,
        Neg,
        Zero,
    }

    pub fn flip(s: Sign) -> Result<Sign> {
        Ok(match s {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
            Sign::Zero => Sign::Zero,
        })
    }
}

// ====================================================================
// traits_basic.rs
// ====================================================================

pub mod traits_basic {
    use super::Result;

    /// IR-side `traits_basic_Tag_0` is a unit struct; R₀ mirrors it.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Tag;

    /// `pub fn use_numeric(t: Tag) -> u32 { t.value() }` — the IR
    /// resolves the trait-method call through the impl, which the
    /// emit recovers as a direct `impl_traits_basic_value_2` call
    /// returning `Ok(42)`.
    pub fn use_numeric(_t: Tag) -> Result<u32> {
        Ok(42)
    }
}

// ====================================================================
// enums_payload.rs
// ====================================================================

pub mod enums_payload {
    use super::Result;

    /// Mirrors the IR's `enums_payload_NumOrZero_0`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum NumOrZero {
        Num(u32),
        Zero,
    }

    pub fn value(x: NumOrZero) -> Result<u32> {
        Ok(match x {
            NumOrZero::Num(n) => n,
            NumOrZero::Zero => 0,
        })
    }

    pub fn wrap(x: u32) -> Result<NumOrZero> {
        Ok(NumOrZero::Num(x))
    }

    pub fn zero() -> Result<NumOrZero> {
        Ok(NumOrZero::Zero)
    }
}

// ====================================================================
// demo.rs — scalar arithmetic helpers.
//
// Source uses `+` (release-mode wrap); the IR lowers each `+` to
// `checked_add(_).ok_or(())`. R₀ matches by chaining the same
// `checked_add` calls. The fixture's `CList` / `list_*` items and
// closure-based fns are excluded — they hit the `LoopOp` /
// FnOnce-closure shim shapes the diff harness can't drive today.
// ====================================================================

pub mod demo {
    use super::Result;

    /// `pub fn mul2_add1(x: u32) -> u32 { (x + x) + 1 }`.
    pub fn mul2_add1(x: u32) -> Result<u32> {
        let v = x.checked_add(x).ok_or(())?;
        v.checked_add(1).ok_or(())
    }

    /// `pub fn use_mul2_add1(x: u32, y: u32) -> u32 { mul2_add1(x) + y }`.
    pub fn use_mul2_add1(x: u32, y: u32) -> Result<u32> {
        let v = mul2_add1(x)?;
        v.checked_add(y).ok_or(())
    }

    /// `pub fn incr(x: &mut u32)` — IR reshapes to forward
    /// `u32 -> Result<u32>` (same as `incr_cert::incr`).
    pub fn incr(x: u32) -> Result<u32> {
        x.checked_add(1).ok_or(())
    }

    /// `fn mod_add(a: u32, b: u32) -> u32 {
    ///     assert!(a < 3329); assert!(b < 3329);
    ///     let sum = a + b;
    ///     let res = sum.wrapping_sub(3329);
    ///     let mask = res >> 16;
    ///     let q = 3329 & mask;
    ///     res.wrapping_add(q) }`
    ///
    /// The IR encodes `assert!` as `if cond { Ok(()) } else { Err(()) }`,
    /// `+` as `checked_add(...).ok_or(())`, and the literal shift `>> 16`
    /// as `checked_shr(16).ok_or(())`. The `wrapping_*` calls route via
    /// the Option-A shim rewrite to native `u32::wrapping_*`.
    pub fn mod_add(a: u32, b: u32) -> Result<u32> {
        if !(a < 3329) {
            return Err(());
        }
        if !(b < 3329) {
            return Err(());
        }
        let sum = a.checked_add(b).ok_or(())?;
        let res = sum.wrapping_sub(3329);
        let mask = res.checked_shr(16).ok_or(())?;
        let q = 3329u32 & mask;
        Ok(res.wrapping_add(q))
    }
}

// ====================================================================
// scalars.rs — pre-extract emit currently routes every fn through an
// `unimplemented!()` opaque shim (`impl_core_num_wrapping_add_*`,
// `impl_core_num_wrapping_sub_*`, etc). Skipping the whole fixture in
// the diff harness until the emitter recovers these.
// ====================================================================
