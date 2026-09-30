//@ [!lean] skip
//@ [lean] aeneas-args=-core-models-lib
//@ [lean] subdir=CoreModelsLib
//! `-core-models-lib` drops the allocators left by `hide_allocator`, but must
//! keep phantom type parameters like the one of `size_of<T>`.

// Keep the type argument.
pub fn size_of_concrete() -> usize {
    core::mem::size_of::<u32>()
}

pub fn size_of_generic<T>() -> usize {
    core::mem::size_of::<T>()
}

pub fn align_of_generic<T>() -> usize {
    core::mem::align_of::<T>()
}

// Drop the allocator.
pub fn vec_push(mut v: Vec<u32>) -> Vec<u32> {
    v.push(0);
    v
}

pub fn vec_len(v: &Vec<u32>) -> usize {
    v.len()
}

// The allocator appears in the impl header through `IntoIter<T, A>`.
pub fn vec_into_iter(v: Vec<u32>) -> std::vec::IntoIter<u32> {
    v.into_iter()
}
