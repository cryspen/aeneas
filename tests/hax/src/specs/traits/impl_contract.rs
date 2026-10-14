// Impl-level contracts: checked as standalone specs only. On an unannotated
// trait (`Foo`): only the standalone spec, no warning. On an annotated trait
// method (`G::g`): the trait-level contract gives the Lawful field, the
// impl-level one a warning and the independent standalone spec.

use hax_lib::*;

trait Foo {
    fn f(&self) -> u32;
}

#[hax_lib::attributes]
impl Foo for u32 {
    #[requires(*self < 100)]
    #[ensures(|res| res == *self + 1)]
    fn f(&self) -> u32 {
        *self + 1
    }
}

#[hax_lib::attributes]
trait G {
    #[ensures(|res| res > 0)]
    fn g(&self) -> u32;
}

#[hax_lib::attributes]
impl G for u32 {
    #[requires(*self < 10)]
    #[ensures(|res| res == *self + 1)]
    fn g(&self) -> u32 {
        *self % 10 + 1
    }
}
