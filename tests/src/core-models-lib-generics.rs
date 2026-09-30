//@ [!lean] skip
//@ [lean] aeneas-args=-core-models-lib
//@ [lean] subdir=CoreModelsLib
//! `-core-models-lib` drops the allocators left by `hide_allocator`, but must
//! keep phantom type parameters like the one of `size_of<T>`.
use std::collections::VecDeque;
use std::rc::Rc;
use std::sync::Arc;

// Keep the type argument.
pub fn size_of_concrete() -> usize {
    core::mem::size_of::<u32>()
}

pub fn size_of_generic<T>() -> usize {
    core::mem::size_of::<T>()
}

pub fn size_of_vec<T>() -> usize {
    core::mem::size_of::<Vec<T>>()
}

pub fn align_of_generic<T>() -> usize {
    core::mem::align_of::<T>()
}

pub fn needs_drop_generic<T>() -> bool {
    core::mem::needs_drop::<T>()
}

pub fn empty_iter<T>() -> core::iter::Empty<T> {
    core::iter::empty::<T>()
}

// Drop the allocator of the impl.
pub fn vec_push(mut v: Vec<u32>) -> Vec<u32> {
    v.push(0);
    v
}

pub fn vec_push_generic<T>(v: &mut Vec<T>, x: T) {
    v.push(x)
}

pub fn vec_len(v: &Vec<u32>) -> usize {
    v.len()
}

pub fn vec_deref(v: &Vec<u32>) -> core::slice::Iter<'_, u32> {
    v.iter()
}

pub fn vec_into_boxed_slice(v: Vec<u32>) -> Box<[u32]> {
    v.into_boxed_slice()
}

// The impl also has an `A: Clone` clause.
pub fn vec_clone(v: &Vec<u32>) -> Vec<u32> {
    v.clone()
}

pub fn rc_clone(r: &Rc<u32>) -> Rc<u32> {
    r.clone()
}

pub fn arc_clone(a: &Arc<u32>) -> Arc<u32> {
    a.clone()
}

// Two allocators, `A1` and `A2`.
pub fn vec_eq(a: &Vec<u32>, b: &Vec<u32>) -> bool {
    a == b
}

// The allocator appears in the impl header through `IntoIter<T, A>`.
pub fn vec_into_iter(v: Vec<u32>) -> std::vec::IntoIter<u32> {
    v.into_iter()
}

// The `IntoIterator` impl has an implied `Iterator for IntoIter<T, A>` ref.
pub fn vec_extend(v: &mut Vec<u32>, w: Vec<u32>) {
    v.extend(w)
}

// Drop the allocator of the method `<[T]>::into_vec<A>`.
pub fn slice_into_vec(b: Box<[u32]>) -> Vec<u32> {
    b.into_vec()
}

pub fn vec_macro() -> Vec<u32> {
    vec![1, 2, 3]
}

// Keep the allocator of `VecDeque`, which `hide_allocator` does not hide.
pub fn vecdeque_push(d: &mut VecDeque<u32>) {
    d.push_back(0)
}
