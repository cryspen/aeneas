#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code)]

// ---- passing unit test (all asserts hold) ----
#[verify::test]
pub fn test_pass() {
    let x = 2u32.wrapping_add(3);
    assert!(x == 5);
}

// ---- failing-assert unit test (native panics at the assert) ----
#[verify::test]
pub fn test_fail_assert() {
    let x = 2u32.wrapping_add(3);
    assert!(x == 6);
}

// ---- checked arithmetic overflow (no wrapping): u32::MAX + 1 ----
#[verify::test]
pub fn test_overflow() {
    let a: u32 = u32::MAX;
    let b: u32 = 1;
    let _c = a + b; // checked add in aeneas; native panics only with overflow checks on
}

// ---- array out of bounds ----
#[verify::test]
pub fn test_oob() {
    let arr = [1u32, 2, 3];
    let i = 5usize;
    let _v = arr[i];
}

// ---- division by zero ----
#[verify::test]
pub fn test_div0() {
    let a: u32 = 10;
    let b: u32 = 0;
    let _c = a / b;
}

// ---- value-returning function (no #assert emitted) ----
pub fn test_value() -> u32 {
    let x = 2u32.wrapping_add(3);
    x
}

// ---- value-returning that overflows ----
pub fn test_value_ovf() -> u32 {
    let a: u32 = u32::MAX;
    a + 1
}
