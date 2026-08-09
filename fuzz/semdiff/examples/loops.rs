#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code)]

// while loop (computable via Aeneas `loop` combinator)
#[verify::test]
pub fn test_while_sum() {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    while i < 5 {
        s = s.wrapping_add(i);
        i += 1;
    }
    assert!(s == 10);
}

// while loop with a failing assert
#[verify::test]
pub fn test_while_fail() {
    let mut i: u32 = 0;
    while i < 3 { i += 1; }
    assert!(i == 99);
}

// range-for loop (NONCOMPUTABLE: uses core::iter::range::Step axioms)
#[verify::test]
pub fn test_for_range() {
    let mut x: u32 = 0;
    for _ in 0u32..5u32 { x = x.wrapping_add(1); }
    assert!(x == 5);
}
