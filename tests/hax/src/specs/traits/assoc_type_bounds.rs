// An associated type with a (non-recursive) trait bound. `first_bar` has a
// generic binder on the trait with the associated type; `Box1`'s generic
// impl sets the associated type to its parameter, whose bound is a clause.
// Its other clause, `T: Copy`, is a marker trait: no Lawful binder ([P17] 3).

use hax_lib::*;

#[hax_lib::attributes]
trait Bar {
    #[ensures(|res| res < 10)]
    fn bar(&self) -> u32;
}

#[hax_lib::attributes]
trait Container {
    type Item: Bar;

    #[ensures(|item| item.bar() < 10)]
    fn first(&self) -> Self::Item;
}

struct One {
    x: u32,
}

impl Bar for u32 {
    fn bar(&self) -> u32 {
        0
    }
}

impl Container for One {
    type Item = u32;

    fn first(&self) -> u32 {
        self.x
    }
}

struct Box1<T>(T);

impl<T: Bar + Copy> Container for Box1<T> {
    type Item = T;

    fn first(&self) -> T {
        self.0
    }
}

#[ensures(|res| res < 10)]
fn first_bar<C: Container>(c: &C) -> u32 {
    c.first().bar()
}
