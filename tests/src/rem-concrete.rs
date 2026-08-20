//@ [!lean] skip
//@ [lean] aeneas-args=-test-units
//! Concrete evaluation of the signed remainder: these unit functions must not
//! panic in the concrete interpreter (see `rem-min-overflow.rs` for the
//! overflowing case).

pub fn rem_min_one() {
    let x: i32 = -2147483648;
    let y: i32 = 1;
    let _ = x % y;
}

pub fn rem_min_minus_two() {
    let x: i32 = -2147483648;
    let y: i32 = -2;
    let _ = x % y;
}

pub fn rem_min_plus_one_minus_one() {
    let x: i32 = -2147483647;
    let y: i32 = -1;
    let _ = x % y;
}

pub fn rem_negative() {
    let x: i32 = -7;
    let y: i32 = 3;
    let _ = x % y;
}
