//! M9.5i fixture: minimal generic enum + generic function.
//!
//! `MyOption<T>` is a payload-bearing generic enum (the parametric
//! equivalent of M9.5e's NumOrZero). `get` is a generic function
//! that matches on `MyOption<T>` and returns the payload or the
//! default — exercising type-variable plumbing on signature,
//! match-arm payload binder, and per-arm RHS expressions.
//!
//! No trait bounds, no Box, no recursion.

pub enum MyOption<T> {
    MySome(T),
    MyNone,
}

pub fn get<T>(x: MyOption<T>, default: T) -> T {
    match x {
        MyOption::MySome(t) => t,
        MyOption::MyNone => default,
    }
}
