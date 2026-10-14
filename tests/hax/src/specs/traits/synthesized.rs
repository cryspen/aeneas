// Annotated traits with one condition per method, no impl: the other
// condition is synthesized as `ok true`. The result type of a synthesized post
// is rewritten into the generics of the decoration fns.

use hax_lib::*;

#[hax_lib::attributes]
trait Gen {
    // Post only: `U` is only in the result, explicit in the synthesized pre
    #[ensures(|_| true)]
    fn pick<U>() -> Option<U>;

    // A method type parameter in the result
    #[requires(true)]
    fn id<U>(&self, u: U) -> U;

    // `&mut self`: the back value is in the result
    #[requires(x < 100)]
    fn add(&mut self, x: u32) -> u32;

    // A const generic in the result
    #[requires(true)]
    fn arr<const N: usize>(&self) -> [u32; N];
}

// A trait type parameter in the result, after `Self_`
#[hax_lib::attributes]
trait Tg<T> {
    #[requires(true)]
    fn get(&self) -> T;
}

// An associated type in the result: `Self_Item` in the trait, `Clause0_Item`
// in the decoration fns
#[hax_lib::attributes]
trait Assoc {
    type Item;

    #[requires(true)]
    fn item(&self) -> Self::Item;
}
