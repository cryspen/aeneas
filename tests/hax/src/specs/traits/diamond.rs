// `C: A + B` with `B: A`: `A` is reachable from `C` along two paths.

use hax_lib::*;

#[hax_lib::attributes]
trait A {
    #[ensures(|res| res >= 1 && res <= 100)]
    fn a(&self) -> usize;
}

trait B: A {
    fn b(&self) -> usize;
}

#[hax_lib::attributes]
trait C: A + B {
    #[ensures(|res| res == self.a())]
    fn c(&self) -> usize;
}

impl A for u8 {
    fn a(&self) -> usize {
        1
    }
}

impl B for u8 {
    fn b(&self) -> usize {
        2
    }
}

impl C for u8 {
    fn c(&self) -> usize {
        self.a()
    }
}

#[ensures(|res| res >= 1 && res <= 100)]
fn via_b<T: B>(x: &T) -> usize {
    x.a()
}

// `x.a()` goes through `C`'s `A` clause, `via_b(x)` through `C`'s `B`
// clause and then `B`'s `A` clause.
#[ensures(|res| res >= 2)]
fn diamond<T: C>(x: &T) -> usize {
    x.a() + via_b(x)
}
