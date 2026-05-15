//! M9.5e fixture: the smallest payload-bearing enum + match.
//!
//! `NumOrZero` has a payload-bearing variant `Num(u32)` and a
//! nullary variant `Zero`. `value` matches and extracts the
//! payload from the `Num` arm. No generics, no Box, no recursion.

pub enum NumOrZero {
    Num(u32),
    Zero,
}

pub fn value(x: NumOrZero) -> u32 {
    match x {
        NumOrZero::Num(n) => n,
        NumOrZero::Zero => 0,
    }
}
