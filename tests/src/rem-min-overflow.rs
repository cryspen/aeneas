//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-test-units
//! `iN::MIN % -1` overflows and panics in Rust, like `iN::MIN / -1`, even
//! though the mathematical result (`0`) is in range: the concrete interpreter
//! must fail on this unit function.

#[allow(unconditional_panic, arithmetic_overflow)]
pub fn rem_min_minus_one() {
    let x: i32 = -2147483648;
    let y: i32 = -1;
    let _ = x % y;
}
