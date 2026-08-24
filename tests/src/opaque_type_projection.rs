//@ [!lean] skip
//@ [lean] known-failure
//@ charon-args=--opaque opaque_type_projection::Foo
// A retained function body that constructs a value of a type made *opaque*
// (here via Charon's `--opaque`, which erases the type's fields). Building the
// aggregate needs the instantiated field types, and Charon's field getter
// raises a raw `Invalid_argument` ("Can't get the list of fields of this adt")
// because the opaque definition has no fields.
//
// Regression: this previously aborted the translation of the *whole crate* with
// an uncaught `Invalid_argument` (it escaped the per-function `CFailure`
// containment). It is now contained: the field getters in `Substitute` route
// the failure through `[%craise]`, naming the offending ADT. Without
// `-abort-on-error` the projecting function is skipped with a warning and the
// rest of the crate still translates; with `-abort-on-error` (as this test
// runs) the failure is reported as a clean hard error, below.

pub struct Foo {
    pub x: u32,
    pub y: u32,
}

pub fn make_foo(a: u32, b: u32) -> Foo {
    Foo { x: a, y: b }
}

pub fn main() {}
