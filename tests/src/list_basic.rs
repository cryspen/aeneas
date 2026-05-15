//! M9.5j fixture: minimal recursive enum + recursive function.
//!
//! `List` is a non-generic singly-linked list with `u32` payload.
//! `list_len` is the canonical recursive walk — exercises Box<T>
//! translation (the recursive payload), the deref `*tail` to get
//! a `List` out of `Box<List>`, and a recursive self-call.
//!
//! Non-generic to keep the chunk focused (generics already work
//! per M9.5i; this isolates Box + recursion).

pub enum List {
    Cons(u32, Box<List>),
    Nil,
}

pub fn list_len(xs: List) -> u32 {
    match xs {
        List::Nil => 0,
        List::Cons(_, tail) => list_len(*tail).wrapping_add(1),
    }
}
