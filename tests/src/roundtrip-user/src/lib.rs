//! The *consumer* half of the `-emit-json` / `-external-names` round trip: one
//! use of each kind of definition `roundtrip-lib` provides.
//!
//! What the golden asserts is what is *absent*. Translated without
//! `-external-names`, this crate re-declares everything it touches - an
//! `axiom roundtrip_lib.add_one`, a second copy of `structure
//! roundtrip_lib.Counter`, and so on - because the definitions belong to
//! another crate. Translated with the manifest, it imports `RoundtripLib` and
//! calls the real definitions, so none of those declarations appear.

use roundtrip_lib::{add_one, sum_to, Bound, Counter, Step, START};

pub fn use_fun(x: u32) -> u32 {
    add_one(x)
}

pub fn use_loop_fun(n: u32) -> u32 {
    sum_to(n)
}

/// `START` is total, so this reads `ok roundtrip_lib.START`. Had the manifest
/// not carried `can_fail: false`, the value would be bound monadically instead.
pub fn use_global() -> u32 {
    START
}

pub fn use_type(c: Counter) -> Counter {
    c
}

/// The variants are named `roundtrip_lib.Bound.Below` and `.Above` here, which
/// is only right because the prefix comes from the manifest rather than from
/// what this crate would have called the type.
pub fn use_enum(b: &Bound) -> u32 {
    match b {
        Bound::Below => 0,
        Bound::Above => 1,
    }
}

/// Resolves through the `trait_impls` bucket, whose entries are registered
/// under the trait applied to the implementation's arguments
/// (`roundtrip_lib::Step<roundtrip_lib::Counter>`) rather than under the
/// implementation's own path.
pub fn use_trait(c: &Counter) -> u32 {
    c.step()
}

/// The three `trait_items` kinds, reached through a bound rather than through a
/// known implementation: the method, the associated constant, and the parent
/// clause which `Step: Base` introduces.
pub fn use_trait_items<T: Step>(t: &T) -> u32 {
    t.step() + T::STRIDE + t.base()
}
