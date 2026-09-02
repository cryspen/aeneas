//! The *provider* half of the `-emit-json` / `-external-names` round trip.
//!
//! This crate is translated with `-emit-json`, which writes
//! `tests/lean/RoundtripLib/translation.json` next to the Lean it generates.
//! `roundtrip-user` is then translated with that file passed to
//! `-external-names`, so its calls into this crate land on the names below
//! instead of on axioms of its own.
//!
//! One definition of each kind the manifest has a bucket for.

pub struct Counter {
    pub value: u32,
}

/// The manifest names the type but not its variants: a consumer recomputes
/// those from the LLBC, prefixed with the name the manifest gives.
pub enum Bound {
    Below,
    Above,
}

/// A total global: extracted as `U32`, not as `Result U32`. The manifest says
/// so through `can_fail`, and a consumer which missed it would wrap the value
/// twice.
pub const START: u32 = 7;

pub trait Base {
    fn base(&self) -> u32;
}

/// A parent clause, an associated constant and a method - the three kinds of
/// trait item the `trait_items` bucket carries.
pub trait Step: Base {
    const STRIDE: u32;

    fn step(&self) -> u32;
}

impl Base for Counter {
    fn base(&self) -> u32 {
        self.value
    }
}

impl Step for Counter {
    const STRIDE: u32 = 2;

    fn step(&self) -> u32 {
        self.value
    }
}

pub fn add_one(x: u32) -> u32 {
    x + 1
}

/// Extracted as three Lean declarations - the function, the loop and its body -
/// which the manifest reports as three `functions` rows sharing this name. The
/// two loop rows carry a `loop` key, and a reader which registered them would
/// map `sum_to` to a declaration of a different arity.
pub fn sum_to(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += i;
        i += 1;
    }
    s
}
