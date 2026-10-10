// A trait method with its own generics and trait clause.

use hax_lib::*;

#[hax_lib::attributes]
trait Bar {
    #[ensures(|res| res < 10)]
    fn bar(&self) -> u32;
}

#[hax_lib::attributes]
trait Foo {
    #[requires(u.bar() < 5)]
    #[ensures(|res| res < 5)]
    fn f<U: Bar>(&self, u: &U) -> u32;
}

impl Bar for u32 {
    fn bar(&self) -> u32 {
        0
    }
}

impl Foo for u32 {
    fn f<U: Bar>(&self, u: &U) -> u32 {
        u.bar()
    }
}
