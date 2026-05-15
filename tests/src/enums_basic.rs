//! M9.5d fixture: the smallest enum + match shape.
//!
//! `Sign` is a 3-variant C-style enum (no payload). `flip` matches
//! on it and returns another variant. This forces the cert/checker
//! to handle: enum type-decl emission, variant-discrimination in
//! the match, and per-arm expression translation. No generics,
//! no Box, no recursion.

pub enum Sign {
    Pos,
    Neg,
    Zero,
}

pub fn flip(s: Sign) -> Sign {
    match s {
        Sign::Pos => Sign::Neg,
        Sign::Neg => Sign::Pos,
        Sign::Zero => Sign::Zero,
    }
}
