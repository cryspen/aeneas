//! M9 cert fixtures: field borrows, index borrows, and reborrow chains.
//!
//! Each function exercises a distinct LLBC# borrow shape:
//! * `set_fst`: `&mut pair.fst` — Field projection on a borrow target.
//! * `set_idx`: `&mut xs[i]` — ProjIndex on a borrow target.
//! * `reborrow_chain`: `let r = &mut x; let s = &mut *r;` — nested mut
//!   borrows, the canonical EvReborrow trigger.

pub struct Pair {
    pub fst: u32,
    pub snd: u32,
}

pub fn set_fst(p: &mut Pair, v: u32) {
    p.fst = v;
}

pub fn set_idx(xs: &mut [u32; 4], i: usize, v: u32) {
    xs[i] = v;
}

pub fn reborrow_chain(x: &mut u32) {
    let s: &mut u32 = &mut *x;
    *s = 7;
}
