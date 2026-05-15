//! M9.5l fixture: minimal trait + impl + direct method call.
//!
//! `Numeric` has one method `value()` returning a `u32`. `Tag` is a
//! unit struct implementing `Numeric`. `use_numeric` calls
//! `Tag::value()` through a concrete `Tag` value — no generic
//! dispatch, no dyn, no trait bounds. The simplest possible trait
//! shape that still exercises trait-decl emission, impl-decl
//! emission, and method resolution.

pub trait Numeric {
    fn value(&self) -> u32;
}

pub struct Tag;

impl Numeric for Tag {
    fn value(&self) -> u32 {
        42
    }
}

pub fn use_numeric(t: Tag) -> u32 {
    t.value()
}
