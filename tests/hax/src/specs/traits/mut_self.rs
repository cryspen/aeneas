// An annotated `&mut self` method. `get` is not annotated.

use hax_lib::*;

#[hax_lib::attributes]
trait Counter {
    fn get(&self) -> u32;

    #[requires(self.get() < 100)]
    #[ensures(|_| future(self).get() == self.get() + 1)]
    fn incr(&mut self);
}

impl Counter for u32 {
    fn get(&self) -> u32 {
        *self
    }

    fn incr(&mut self) {
        *self += 1
    }
}
