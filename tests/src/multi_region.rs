//! M12.2b fixture: helpers with distinct lifetimes so each `&mut`
//! input lives in its own region. The standard backend translates
//! these into *two* backward closures, one per input lifetime —
//! whereas single-lifetime helpers (e.g. `calls::choose`) collapse
//! both inputs into one closure.
//!
//! `swap_pair` is a no-op rebind that returns the two inputs through
//! their original lifetimes. Calling `use_swap_pair` and writing
//! through *both* returned references forces the cert to emit one
//! `EvEndAbs` per region, with separate closures bound on the Lean
//! side.

pub fn swap_pair<'a, 'b>(x: &'a mut u32, y: &'b mut u32) -> (&'a mut u32, &'b mut u32) {
    (x, y)
}

pub fn use_swap_pair(x: &mut u32, y: &mut u32) {
    let (rx, ry) = swap_pair(x, y);
    *rx = 7;
    *ry = 9;
}
