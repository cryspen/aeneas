//@ [!lean] skip
//@ [lean] subdir=CoreModelsLib
//@ [lean] aeneas-args=-core-models-lib
//! `-core-models-lib`: items of `core`/`alloc`/`std` come from the external
//! `CoreModels` library instead of the Aeneas standard library. This file only
//! pins the extracted code: it is not built in `tests/lean` because
//! `CoreModels` is not a dependency there.

/// The derived `Eq` impl must not mention `assert_fields_are_eq`.
#[derive(PartialEq, Eq)]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

/// `Box::new` stays the identity.
pub fn box_new(x: u32) -> Box<u32> {
    Box::new(x)
}

/// `Vec` methods carry a hidden allocator parameter, whose dangling type
/// parameter and trait clause are filtered out (with fewer trait clauses than
/// type parameters).
pub fn vec_push(mut v: Vec<u32>, x: u32) -> Vec<u32> {
    v.push(x);
    v
}

pub fn vec_sum(v: Vec<u32>) -> u32 {
    let mut s = 0u32;
    for x in v.into_iter() {
        s = s.wrapping_add(x);
    }
    s
}

pub trait Op {
    fn apply(x: u8) -> u8;
}

/// The generics of local items are never filtered: the call to `callee` keeps
/// its `C: Op` argument.
pub fn callee<C: Op>(x: u8) -> u8 {
    C::apply(x)
}

pub fn caller<C: Op>(x: u8) -> u8 {
    callee::<C>(x)
}

/// The loop body is extracted as its own function carrying `C: Op`.
pub fn one_loop_unused<C: Op>(xs: &[u8]) -> u8 {
    let mut acc = 0u8;
    for i in 0..xs.len() {
        acc = acc.wrapping_add(xs[i]);
    }
    C::apply(acc)
}

/// A local impl of a non-local trait.
impl Default for Pair {
    fn default() -> Self {
        Pair { a: 0, b: 0 }
    }
}

pub fn array_to_slice(a: &[u32; 4]) -> &[u32] {
    a.as_slice()
}

pub fn array_repeat(x: u32) -> [u32; 4] {
    [x; 4]
}

/// `Some` used as a function: a constructor function, a non-local item.
pub fn option_some(xs: Vec<u32>) -> Vec<Option<u32>> {
    xs.into_iter().map(Some).collect()
}
