// Associated constants used in contracts (hax only takes contracts on methods,
// not on constants): in the conditions of the trait, of an impl method (the
// concrete constant) and of a generic caller, with a default value, and through
// a subtrait.

use hax_lib::*;

#[hax_lib::attributes]
trait Bounded {
    const MAX: u32;

    // A default value
    const MIN: u32 = 0;

    #[requires(x < Self::MAX)]
    #[ensures(|r| r <= Self::MAX)]
    fn clamp(&self, x: u32) -> u32;
}

#[hax_lib::attributes]
impl Bounded for u32 {
    const MAX: u32 = 100;

    // Not `Self::MAX`: hax-lib puts the condition in a fn nested in the method,
    // where `Self` is not in scope (it only rewrites associated types)
    #[requires(x < <u32 as Bounded>::MAX)]
    fn clamp(&self, x: u32) -> u32 {
        x
    }
}

// The constants of the supertrait, through the subtrait
#[hax_lib::attributes]
trait Scaled: Bounded {
    #[requires(Self::MIN <= x && x <= Self::MAX)]
    #[ensures(|r| r <= Self::MAX)]
    fn scale(&self, x: u32) -> u32;
}

impl Scaled for u32 {
    fn scale(&self, x: u32) -> u32 {
        x
    }
}

// A generic caller: its contract mentions `T::MAX`
#[requires(x < T::MAX)]
#[ensures(|r| r <= T::MAX)]
fn use_clamp<T: Bounded>(t: &T, x: u32) -> u32 {
    t.clamp(x)
}
