//! M9.5g fixture: minimal slice indexing patterns.
//!
//! `get_first` reads from an immutable slice; `set_idx_slice` writes
//! through a mutable slice. Together they exercise the LLBC slice
//! type and the `core::slice::SliceIndex` desugaring on both sides.
//! No generics, no Vec, no iterators — those are later chunks.

pub fn get_first(xs: &[u32]) -> u32 {
    xs[0]
}

pub fn set_idx_slice(xs: &mut [u32], i: usize, v: u32) {
    xs[i] = v;
}
