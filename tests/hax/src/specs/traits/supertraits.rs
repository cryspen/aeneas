// `B: A`, both annotated. `B::b`'s contract reaches `A` through `self`.
// `Cc: B`: `Cc::c`'s contract reaches `A` through two parent projections.

use hax_lib::*;

#[hax_lib::attributes]
trait A {
    #[ensures(|res| res >= 1)]
    fn a(&self) -> usize;
}

#[hax_lib::attributes]
trait B: A {
    #[requires(self.a() < 100)]
    #[ensures(|res| res > self.a())]
    fn b(&self) -> usize;
}

#[hax_lib::attributes]
trait Cc: B {
    #[ensures(|res| res > self.a())]
    fn c(&self) -> usize;
}

impl A for u8 {
    fn a(&self) -> usize {
        1
    }
}

impl B for u8 {
    fn b(&self) -> usize {
        self.a() + 1
    }
}

impl Cc for u8 {
    fn c(&self) -> usize {
        self.b()
    }
}

// Generic caller of both methods: `x.a()` goes through `B`'s `A` clause
// (`BInstLawful.AInstLawful.a_spec`), `x.b()` through `b_spec`, whose pre is
// this fn's pre. No underflow: `b`'s post says `x.b() > x.a()`.
#[requires(x.a() < 100)]
#[ensures(|res| res >= 1)]
fn via_b<T: B>(x: &T) -> usize {
    x.b() - x.a()
}

// Concrete caller of both methods, on the `u8` impls (their `.Lawful`
// theorems).
#[requires(x.a() < 100)]
#[ensures(|res| res >= 1)]
fn via_u8(x: u8) -> usize {
    x.b() - x.a()
}
