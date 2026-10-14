// A trait with no annotated method of its own, with an annotated
// supertrait: its `Lawful` only has the parent field.

use hax_lib::*;

#[hax_lib::attributes]
trait A {
    #[ensures(|res| res > 0)]
    fn a(&self) -> u32;
}

trait B: A {
    fn b(&self) -> u32;
}

impl A for u32 {
    fn a(&self) -> u32 {
        1
    }
}

impl B for u32 {
    fn b(&self) -> u32 {
        0
    }
}
