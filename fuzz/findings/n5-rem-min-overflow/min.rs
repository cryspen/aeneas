// i32::MIN % -1 overflows in Rust (panics with overflow-checks), but Aeneas's
// model returns 0. Native (panic) vs Lean (ok 0) must MISMATCH.
pub fn test_rem_min() {
    let x: i32 = i32::MIN;
    let y: i32 = -1;
    let r = x % y;
    assert!(r == 0);
}
// control: a normal remainder that agrees on both sides.
pub fn test_rem_ok() {
    let r: i32 = 17 % 5;
    assert!(r == 2);
}
