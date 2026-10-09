// Unit arguments are extracted as `_` binders: the specs must still pass them,
// as `()`.
use hax_lib::*;

trait Size {
    fn len(&self) -> usize;
}

// `self : ()`
#[hax_lib::attributes]
impl Size for () {
    #[ensures(|_| true)]
    fn len(&self) -> usize {
        0
    }
}

#[ensures(|result| result == 0)]
fn named(x: ()) -> usize {
    0
}

// The unit argument comes before another one.
#[requires(y < 100)]
#[ensures(|result| result == y)]
fn before_other(x: (), y: u32) -> u32 {
    y
}
