// Just an annotated trait, no impl. `g` is not annotated, `h` only has a
// pre (its post defaults to `ok true`).

use hax_lib::*;

#[attributes]
trait Foo {
    #[requires(x < 100)]
    #[ensures(|res| res > x)]
    fn f(&self, x: u32) -> u32;

    fn g(&self) -> u32;

    #[requires(x > 0)]
    fn h(&self, x: u32) -> u32;
}
