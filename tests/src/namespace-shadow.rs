//@ [!lean] skip
//! Test: a variable shadowed by a namespace with the same name.
//!
//! A Rust module `cshadow` becomes the Lean namespace `cshadow`. If a function
//! binds a variable also called `cshadow`, then `cshadow.f` is parsed as a
//! projection out of the variable instead of a reference to the qualified
//! constant, and elaboration fails. The variable must hence be renamed.

pub mod cshadow {
    pub fn f(x: usize) -> usize {
        x
    }

    pub fn g(cshadow: usize) -> usize {
        f(cshadow)
    }
}

/// A namespace nested two levels deep: `outer` is not a name on its own, only
/// the first component of `outer.inner.f`, which a variable called `outer`
/// would turn into a projection.
pub mod outer {
    pub mod inner {
        pub fn f(x: usize) -> usize {
            x
        }
    }
}

pub fn deep(outer: usize) -> usize {
    outer::inner::f(outer)
}
