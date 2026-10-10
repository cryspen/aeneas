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

pub struct Point {
    pub x: u32,
    pub y: u32,
}

// Field accesses in the conditions
#[requires(p.x < 100 && p.y < 100)]
#[ensures(|result| result == p.x + p.y)]
fn sum_fields(p: Point) -> u32 {
    p.x + p.y
}

pub enum Shape {
    Dot,
    Line(u32),
}

// A `match` on an enum argument in the precondition
#[requires(match s { Shape::Dot => true, Shape::Line(l) => l < 100 })]
#[ensures(|result| result <= 100)]
fn shape_len(s: Shape) -> u32 {
    match s {
        Shape::Dot => 0,
        Shape::Line(l) => l + 1,
    }
}
