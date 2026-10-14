// A generic function bounded by a built-in trait, and a trait with a
// built-in supertrait. Local impls of foreign traits: derived `Clone` on a
// non-generic and on a generic struct, hand-written `Default`; the derived
// ones are the `Clone` parents of `Dup` impls. No `BuiltinOrAuto` parent
// ([P17] 1): built-in `Clone`/`Copy` refs (e.g. `Dup for (u32, u32)`) print
// `BuiltinClone`, which is not CoreModels' `Clone`; `Fn*` refs are not
// reachable (closures and fn items get impls, fn pointers are unsupported).

use hax_lib::*;

#[ensures(|_| true)]
fn dup<T: Clone>(x: &T) -> (T, T) {
    (x.clone(), x.clone())
}

#[hax_lib::attributes]
trait Dup: Clone {
    #[ensures(|_| true)]
    fn dup(&self) -> (Self, Self);
}

impl Dup for u32 {
    fn dup(&self) -> (u32, u32) {
        (*self, *self)
    }
}

#[derive(Clone)]
struct One;

impl Default for One {
    fn default() -> Self {
        One
    }
}

impl Dup for One {
    fn dup(&self) -> (One, One) {
        (self.clone(), self.clone())
    }
}

#[derive(Clone)]
struct W<T> {
    x: T,
}

impl Dup for W<u32> {
    fn dup(&self) -> (W<u32>, W<u32>) {
        (self.clone(), self.clone())
    }
}
