// A generic parameter is implicit when it can be inferred from an input type or
// a trait clause. `post` takes the result as an extra input, so it can infer
// parameters that the function it describes has to take explicitly: each of
// them must be applied with its own implicit/explicit information. (`pre` has
// exactly the inputs of the function, so it never diverges from it.)
use hax_lib::*;

// Const generic params
#[requires(0 < x && x < N)]
#[ensures(|result| result < N)]
fn generic<const N: u32>(x: u32) -> u32 {
    N - x
}

// Trait params
trait Val {
    fn value(&self) -> u32;
}

impl Val for u32 {
    fn value(&self) -> u32 {
        *self
    }
}

#[requires(t.value() < 1000 && x < 1000)]
#[ensures(|result| result < 2000)]
fn trait_clause<T: Val>(t: T, x: u32) -> u32 {
    t.value() + x
}

// The same trait clause, in a `where` clause
#[requires(t.value() < 1000)]
#[ensures(|result| result < 1000)]
fn where_clause<T>(t: T) -> u32
where
    T: Val,
{
    t.value()
}

pub struct MyStruct<const N: usize> {
    pub cap: usize,
}

#[hax_lib::attributes]
impl<const N: usize> MyStruct<N> {
    // Associated function (no `self`): `N` only appears in the output type,
    // so it is explicit in the function and in `pre`, implicit in `post`.
    #[requires(k < 100)]
    #[ensures(|_| true)]
    pub fn build(k: usize) -> Self {
        MyStruct { cap: k }
    }

    // Control: a `&self` method, where `N` appears in an input type.
    #[ensures(|_| true)]
    pub fn get(&self) -> usize {
        self.cap
    }
}

pub struct Pair<T, const N: usize> {
    pub fst: T,
}

// A type parameter which only appears in the output type. (Note the dummy
// argument: a condition on a function with no argument at all is dropped,
// see `contracts::no_args`.)
#[ensures(|_| true)]
fn nothing<T>(k: usize) -> Option<T> {
    None
}

// Mixed: `T` is inferable from the inputs, `N` only from the result.
#[ensures(|_| true)]
fn of_fst<T, const N: usize>(t: T) -> Pair<T, N> {
    Pair { fst: t }
}

// Both parameters only appear in the output type.
#[ensures(|_| true)]
fn empty<T, const N: usize>(k: usize) -> Option<Pair<T, N>> {
    None
}

// A trait clause next to a const generic which only appears in the output
// type. No spec: it would be unprovable, since nothing guarantees that
// `T::default()` succeeds.
fn from_default<T: Default, const N: usize>(k: usize) -> Pair<T, N> {
    Pair { fst: T::default() }
}
