// Several functions take dummy arguments (see `generics::nothing`), and most
// items are only there to be extracted.
#![allow(dead_code, unused_variables)]

// The shape of `requires`/`ensures` annotations.
mod contracts;
// How the inputs of a function are passed to its conditions.
mod arguments;
// `&mut` inputs, and `future` in postconditions.
mod mutable_borrows;
// Generic parameters, and which of them the conditions take explicitly.
mod generics;
// Conditions on methods: inherent, of trait impls, provided by traits.
mod traits;
// Names like those of the generated items.
mod naming;
