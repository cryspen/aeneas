// Several functions take dummy arguments (see `implicit_generics::nothing`).
#![allow(unused_variables)]

#[allow(dead_code)]
mod basic {
    use hax_lib::*;

    #[requires(x < 100)]
    fn only_requires(x: u32) -> u32 {
        x + 1
    }

    #[ensures(|result| result == x)]
    fn only_ensures(x: u32) -> u32 {
        x
    }

    #[requires(x < 10)]
    #[ensures(|result| result > x)]
    fn both(x: u32) -> u32 {
        x + 1
    }

    // Unit return with a by-value argument
    #[requires(x < 10)]
    #[ensures(|_| true)]
    fn returns_unit(x: u32) {}

    // No arguments
    #[ensures(|_| true)]
    fn no_args() {
        let _x = 0;
        ()
    }

    // Block expression (with a `let`) inside `requires`
    #[requires({ let bound = x; bound > 10 })]
    fn block_in_requires(x: u32) -> u32 {
        x
    }

    // Pattern directly in the result closure
    #[ensures(|(a, b)| a == x && b == x)]
    fn returns_pair(x: u32) -> (u32, u32) {
        (x, x)
    }
}

#[allow(dead_code)]
mod extra_args {
    use hax_lib::*;

    // Const generic params
    #[requires(0 < x && x < N)]
    #[ensures(|result| result < N)]
    fn generic<const N: u32>(x: u32) -> u32 {
        N - x
    }

    // Trait params
    trait Val {
        fn value(&self) -> u32;
    }

    impl Val for u32 {
        fn value(&self) -> u32 {
            *self
        }
    }

    #[requires(t.value() < 1000 && x < 1000)]
    #[ensures(|result| result < 2000)]
    fn traits<T: Val>(t: T, x: u32) -> u32 {
        t.value() + x
    }
}

#[allow(dead_code)]
mod future {
    use hax_lib::*;

    #[requires(*x < 1000)]
    #[ensures(|_| *future(x) == *x + 1 )]
    fn incr(x: &mut u32) {
        *x += 1;
    }

    #[requires(i < x.len() && x[i] < u32::MAX)]
    #[ensures(|_| {
            let r = future(x);
            r[i] == x[i] + 1})]
    fn incr_i(x: &mut [u32], i: usize) {
        x[i] += 1
    }

    #[requires(*x < 1000 && *y < 1000)]
    // `*x + *y` rather than `x + y`: the latter calls `impl Add<&u32> for &u32`,
    // which hax's core models do not define yet.
    #[ensures(|r| { *future(y) == *x && *future(x) == *y && r == *x + *y})]
    fn swap_and_add(x: &mut u32, y: &mut u32) -> u32 {
        let tmp_x = *x;
        let tmp_y = *y;
        *x = tmp_y;
        *y = tmp_x;
        tmp_x + tmp_y
    }
}

// A generic parameter is implicit when it can be inferred from an input type or
// a trait clause. `post` takes the result as an extra input, so it can infer
// parameters that the function it describes has to take explicitly: each of
// them must be applied with its own implicit/explicit information. (`pre` has
// exactly the inputs of the function, so it never diverges from it.)
#[allow(dead_code)]
mod const_generic_ty {

    pub struct MyStruct<const N: usize> {
        pub cap: usize,
    }

    #[hax_lib::attributes]
    impl<const N: usize> MyStruct<N> {
        // Associated function (no `self`): `N` only appears in the output type,
        // so it is explicit in the function and in `pre`, implicit in `post`.
        #[requires(k < 100)]
        #[ensures(|_| true)]
        pub fn build(k: usize) -> Self {
            MyStruct { cap: k }
        }

        // Control: a `&self` method, where `N` appears in an input type.
        #[ensures(|_| true)]
        pub fn get(&self) -> usize {
            self.cap
        }
    }
}

#[allow(dead_code)]
mod implicit_generics {
    use hax_lib::*;

    pub struct Pair<T, const N: usize> {
        pub fst: T,
    }

    // A type parameter which only appears in the output type. (Note the dummy
    // argument: a condition on a function with no argument at all is dropped,
    // see `basic::no_args`.)
    #[ensures(|_| true)]
    fn nothing<T>(k: usize) -> Option<T> {
        None
    }

    // Mixed: `T` is inferable from the inputs, `N` only from the result.
    #[ensures(|_| true)]
    fn of_fst<T, const N: usize>(t: T) -> Pair<T, N> {
        Pair { fst: t }
    }

    // Both parameters only appear in the output type.
    #[ensures(|_| true)]
    fn empty<T, const N: usize>(k: usize) -> Option<Pair<T, N>> {
        None
    }

    // A trait clause next to a const generic which only appears in the output
    // type. No spec: it would be unprovable, since nothing guarantees that
    // `T::default()` succeeds.
    fn from_default<T: Default, const N: usize>(k: usize) -> Pair<T, N> {
        Pair { fst: T::default() }
    }
}

// Unit arguments are extracted as `_` binders: the specs must still pass them,
// as `()`.
#[allow(dead_code)]
mod unit_args {
    use hax_lib::*;

    trait Size {
        fn len(&self) -> usize;
    }

    // `self : ()`
    #[hax_lib::attributes]
    impl Size for () {
        #[ensures(|_| true)]
        fn len(&self) -> usize {
            0
        }
    }

    #[ensures(|result| result == 0)]
    fn named(x: ()) -> usize {
        0
    }

    // The unit argument comes before another one.
    #[requires(y < 100)]
    #[ensures(|result| result == y)]
    fn before_other(x: (), y: u32) -> u32 {
        y
    }
}

// The conditions of a trait method take one trait clause per supertrait, while
// the method reaches the supertraits through its `Self` clause.
#[allow(dead_code)]
mod supertraits {
    pub trait A {
        fn a(&self) -> usize;
    }

    #[hax_lib::attributes]
    pub trait B: A {
        fn b(&self) -> usize;

        #[requires(self.a() < 100)]
        #[ensures(|res| res == self.a())]
        fn provided(&self) -> usize {
            self.a()
        }
    }

    // A supertrait of a supertrait. The precondition evaluates `self.a()`, which
    // makes the spec provable without knowing anything about `A`'s impls.
    #[hax_lib::attributes]
    pub trait C: B {
        #[requires(self.a() < 100)]
        #[ensures(|res| res == self.a())]
        fn provided_c(&self) -> usize {
            self.a()
        }
    }

    // A generic supertrait.
    pub trait G<T> {
        fn g(&self) -> T;
    }

    // No spec: it would be unprovable, since nothing guarantees that `self.g()`
    // succeeds.
    pub trait H<T>: G<T> {
        fn provided_h(&self) -> T {
            self.g()
        }
    }
}
// Items with names like the generated `foo.pre`/`foo.post`/`foo.spec`/
// `foo.spec.proof` which don't clash (a clash is an error).
#[allow(dead_code)]
mod reserved_names {
    use hax_lib::*;

    #[requires(x < 100)]
    #[ensures(|result| result == x + 1)]
    pub fn foo(x: u32) -> u32 {
        x + 1
    }

    // Same path as the contracted `foo`, but no clash.
    pub mod foo {
        pub fn precondition(x: u32) -> bool {
            x < 100
        }

        pub mod spec {
            pub fn lemma() {}
        }
    }

    // No clash: not the name of a contracted function.
    pub fn proof() {}

    pub mod bar {
        pub fn pre() {}
    }
}
