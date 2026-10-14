// An annotated provided method, overridden by one impl and not by the
// other. `base` is not annotated.

use hax_lib::*;

#[hax_lib::attributes]
trait D {
    fn base(&self) -> u32;

    #[requires(self.base() < 100)]
    #[ensures(|res| res > self.base())]
    fn next(&self) -> u32 {
        self.base() + 1
    }
}

impl D for u32 {
    fn base(&self) -> u32 {
        *self
    }

    fn next(&self) -> u32 {
        *self + 2
    }
}

impl D for u64 {
    fn base(&self) -> u32 {
        0
    }
}
