// The conditions of a trait method take one trait clause per supertrait, while
// the method reaches the supertraits through its `Self` clause.
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

// Conditions on a required method, which has no default body to check them
// against: they could only constrain the impls. Currently dropped: no
// `pre`/`post` is extracted for them.
#[hax_lib::attributes]
pub trait D {
    #[requires(x < 100)]
    #[ensures(|res| res > x)]
    fn required(&self, x: u32) -> u32;
}

impl D for u32 {
    fn required(&self, x: u32) -> u32 {
        x + 1
    }
}
