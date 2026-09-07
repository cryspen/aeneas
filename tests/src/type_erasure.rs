//! An arrow-typed field cannot be translated, so it is replaced by the opaque
//! `Erased` placeholder: the containing type and its callers still translate,
//! instead of the whole type being dropped.

pub struct Handler {
    pub cb: fn(u32) -> u32,
    pub n: u32,
}

pub fn get_n(h: &Handler) -> u32 {
    h.n
}
