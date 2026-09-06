//@ charon-args=--exclude=opaque_trait_impl::{impl opaque_trait_impl::Tr for opaque_trait_impl::S}::m
//! When a trait implementation's method is excluded (or fails to translate), the
//! instance is emitted as an opaque axiom rather than a record with a `sorry`
//! field, so that declarations referring to the instance still typecheck.

pub trait Tr {
    fn m(&self) -> u32;
}

pub struct S;

impl Tr for S {
    fn m(&self) -> u32 {
        0
    }
}
