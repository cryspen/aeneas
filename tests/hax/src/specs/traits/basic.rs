// A trait, two impls, a generic caller and a concrete caller. `make` and
// `zero` are associated fns without `self` (`zero` is nullary).

use hax_lib::*;

#[hax_lib::attributes]
trait Foo {
    #[ensures(|_| true)]
    fn f1(&self) -> bool;

    #[requires(self.f1())]
    #[ensures(|res| res <= 10)]
    fn f2(&self) -> u64;

    #[ensures(|res| res.f1())]
    fn make(x: u32) -> Self;

    #[ensures(|res| res.f1())]
    fn zero() -> Self;
}

impl Foo for u64 {
    fn f1(&self) -> bool {
        *self <= 10
    }

    fn f2(&self) -> u64 {
        *self
    }

    fn make(x: u32) -> u64 {
        (x % 10) as u64
    }

    fn zero() -> u64 {
        0
    }
}

impl Foo for u32 {
    fn f1(&self) -> bool {
        *self <= 10
    }

    fn f2(&self) -> u64 {
        *self as u64
    }

    fn make(x: u32) -> u32 {
        x % 10
    }

    fn zero() -> u32 {
        0
    }
}

#[ensures(|res| res <= 10)]
fn g<T: Foo>(x: T) -> u64 {
    if x.f1() {
        x.f2()
    } else {
        0
    }
}

// Concrete caller.
#[ensures(|res| res <= 10)]
fn h(x: u64) -> u64 {
    g(x)
}
