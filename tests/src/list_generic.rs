//! M9.5k probe: combines M9.5i (generics) and M9.5j (Box + recursion).
//!
//! Tests whether generic recursive enum + generic recursive function
//! work "for free" given that the two underlying features ship green.

pub enum GList<T> {
    GCons(T, Box<GList<T>>),
    GNil,
}

pub fn glist_len<T>(xs: GList<T>) -> u32 {
    match xs {
        GList::GNil => 0,
        GList::GCons(_, tail) => glist_len(*tail).wrapping_add(1),
    }
}
