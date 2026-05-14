//! Three small fixtures for side-by-side backend comparison.

/// Pure identity over a u32. The cert should be empty (no borrows).
pub fn id_u32(x: u32) -> u32 {
    x
}

/// Direct borrow + arithmetic. Real translation: `x + 1`.
/// New backend's M7 placeholder: `.ok x1`.
pub fn incr_val(x: &mut u32) {
    *x += 1;
}

/// Two-arg arithmetic.
pub fn add_u32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}
