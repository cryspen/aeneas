//! M9.5p fixture: minimal tuple + named-field struct aggregate construction.
//!
//! `mk_tuple` constructs a `(u32, u32)` tuple aggregate; `mk_pair`
//! constructs a `Pair { x, y }` named-field struct aggregate. Together
//! they exercise the SymTuple + SymRecord cert events introduced in
//! M9.5p-1 and the matching PExpr.tuple / PExpr.recordLit lowering on
//! the Lean side.

pub struct Pair {
    pub x: u32,
    pub y: u32,
}

pub fn mk_tuple(x: u32, y: u32) -> (u32, u32) {
    (x, y)
}

pub fn mk_pair(x: u32, y: u32) -> Pair {
    Pair { x, y }
}
