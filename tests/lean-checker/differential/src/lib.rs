#![allow(unused_variables, dead_code, unused_parens, unused_mut, non_snake_case)]

//! Differential harness for the aeneas-lean-checker vertical slice.
//!
//! Each cert's generated model is `include!`'d inside its own module
//! to isolate per-crate ADT decls (different crates often define
//! their own `Pair` etc.). The proptests in `tests/diff.rs` import
//! the per-module `_model` fns and compare them to hand-written
//! references on randomised inputs.
//!
//! Phase 1C: the `aggregates_basic` and `reborrows` modules exercise
//! ADT record literals and struct field updates, which the RustEmit
//! backend can now render as real Rust syntax
//! (`Foo { f1: v1, f2: v2 }` and `Foo { field: v, ..base }`).

// --------------------------------------------------------------------
// incr_cert — M8 baseline (no ADTs).
// --------------------------------------------------------------------

pub fn incr_ref(x: u32) -> u32 {
    // M10.0: the cert now carries the `*x += 1` binop, so the model
    // emits `x + 1`. The reference shifts in lock-step.
    x.wrapping_add(1)
}

include!("model.rs");

// --------------------------------------------------------------------
// aggregates_basic — Phase 1C: SymRecord → struct literal.
// --------------------------------------------------------------------

pub mod aggregates_basic {
    #![allow(unused_variables, dead_code, unused_parens, unused_mut, non_snake_case)]

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Pair {
        pub x: u32,
        pub y: u32,
    }

    pub fn mk_pair_ref(x: u32, y: u32) -> Pair {
        Pair { x, y }
    }

    pub fn mk_tuple_ref(x: u32, y: u32) -> (u32, u32) {
        (x, y)
    }

    include!("aggregates_basic_model.rs");
}

// --------------------------------------------------------------------
// reborrows — Phase 1C: structUpdate → Foo { f: v, ..base }.
//
// We don't `include!("reborrows_model.rs")` directly because the
// model also contains `set_idx_model` which emits
// `Array.update(x1, x2, x3)` (Lean dot-call notation). That's a
// separate emitter gap tracked outside Phase 1C. Instead, we copy
// `set_fst_model` here verbatim from the generated file so the ADT
// proptest can run. If/when the dot-call form is fixed elsewhere
// (Phase 1A/1B), this module can switch to `include!`.
// --------------------------------------------------------------------

pub mod reborrows {
    #![allow(unused_variables, dead_code, unused_parens, unused_mut, non_snake_case)]

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Pair {
        pub fst: u32,
        pub snd: u32,
    }

    pub fn set_fst_ref(p: Pair, v: u32) -> Pair {
        let mut p = p;
        p.fst = v;
        p
    }

    // Phase 1C: copy of the `set_fst_model` emitted by aeneas-check
    // from `tests/llbc/reborrows.cert.json`. This is the exact Rust
    // syntax produced by `PExpr.structUpdate base "fst" v (some "Pair")`
    // via `RustEmit.lean`. Kept in source so the ADT proptest can run
    // without needing to fix the unrelated `Array.update` dot-call
    // gap in `set_idx_model`.
    pub fn set_fst_model(x1: Pair, x2: u32) -> Pair {
        Pair { fst: x2, ..x1 }
    }
}
