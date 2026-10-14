// Generic impls, including one of a subtrait whose parent impl is itself
// generic, one with two clauses (on a tuple), and a concrete impl whose
// parent impl is a generic impl applied to another impl (`Single<u64>`).
// `k` has two clauses on different traits.

use hax_lib::*;

#[hax_lib::attributes]
trait Foo {
    #[ensures(|res| res <= 10)]
    fn f(&self) -> u64;
}

#[hax_lib::attributes]
trait Sub: Foo {
    #[ensures(|res| res == self.f())]
    fn s(&self) -> u64;
}

struct Wrapper<T> {
    inner: T,
}

impl Foo for u64 {
    fn f(&self) -> u64 {
        0
    }
}

impl<T: Foo> Foo for Wrapper<T> {
    fn f(&self) -> u64 {
        self.inner.f()
    }
}

impl<T: Sub> Sub for Wrapper<T> {
    fn s(&self) -> u64 {
        self.inner.s()
    }
}

impl<T: Foo, U: Foo> Foo for (T, U) {
    fn f(&self) -> u64 {
        self.0.f()
    }
}

struct Single<T>(T);

impl<T: Foo> Foo for Single<T> {
    fn f(&self) -> u64 {
        self.0.f()
    }
}

impl Sub for Single<u64> {
    fn s(&self) -> u64 {
        self.f()
    }
}

#[ensures(|res| res <= 20)]
fn k<T: Foo, U: Sub>(x: &T, y: &U) -> u64 {
    x.f() + y.s()
}
