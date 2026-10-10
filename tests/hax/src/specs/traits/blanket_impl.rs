// A blanket impl: `Show` for every type `T`, without any bound. Its Lawful
// obligation is generic over `T` and takes no Lawful binder (no impl clause);
// callers reach `Show` through the blanket impl applied to their own type.
// `Tag: Show` has a blanket impl with a clause: its `Show` parent is that
// clause.

use hax_lib::*;

#[hax_lib::attributes]
trait Show {
    #[ensures(|res| res <= 20)]
    fn show(&self) -> u64;
}

impl<T> Show for T {
    fn show(&self) -> u64 {
        7
    }
}

// Generic caller: `Show` comes from the blanket impl at `T` (no clause).
#[ensures(|res| res <= 20)]
fn show_generic<T>(x: &T) -> u64 {
    x.show()
}

// Concrete caller: `Show` comes from the blanket impl at `u64`.
#[ensures(|res| res <= 20)]
fn show_u64(x: u64) -> u64 {
    x.show()
}

trait Tag: Show {}

impl<T: Show> Tag for T {}
