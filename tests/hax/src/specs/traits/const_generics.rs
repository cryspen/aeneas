// A trait with a const generic parameter used in its conditions, two impls
// at different values for the same type, a generic caller at a fixed value,
// and a blanket impl over arrays whose length is the parameter.

use hax_lib::*;

#[hax_lib::attributes]
trait Cg<const N: usize> {
    #[requires(x < N)]
    #[ensures(|res| res <= N)]
    fn f(&self, x: usize) -> usize;
}

impl Cg<4> for u32 {
    fn f(&self, x: usize) -> usize {
        x
    }
}

impl Cg<8> for u32 {
    fn f(&self, x: usize) -> usize {
        x + 1
    }
}

impl<const N: usize> Cg<N> for [u32; N] {
    fn f(&self, _x: usize) -> usize {
        N
    }
}

#[requires(x < 4)]
#[ensures(|res| res <= 4)]
fn use_cg<T: Cg<4>>(t: &T, x: usize) -> usize {
    t.f(x)
}
