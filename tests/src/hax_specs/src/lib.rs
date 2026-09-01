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

    // No arguments
    #[ensures(|_| true)]
    fn no_args() {
        let _x = 0;
        ()
    }

    // Unit return with a by-value argument
    #[requires(x < 10)]
    #[ensures(|_| true)]
    fn returns_unit(x: u32) {}

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

    #[requires(i < x.len())]
    #[ensures(|_| {
            let r = future(x);
            r[i] == x[i] + 1})]
    fn incr_i(x: &mut [u32], i: usize) {
        x[i] += 1
    }

    #[requires(*x < 1000 && *y < 1000)]
    #[ensures(|r| { *future(y) == *x && *future(x) == *y && r == x + y})]
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
    use hax_lib::*;

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

    // A trait clause (which makes `T` implicit, and is passed to `post` too)
    // next to a const generic which only `post` can infer.
    #[requires(k < 100)]
    #[ensures(|_| true)]
    fn from_default<T: Default, const N: usize>(k: usize) -> Pair<T, N> {
        Pair { fst: T::default() }
    }
}
