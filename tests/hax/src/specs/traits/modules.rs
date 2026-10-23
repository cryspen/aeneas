// A trait declared in a nested module and implemented from another module,
// an `impl Trait` argument, and an impl with a `where` clause.

use hax_lib::*;

mod a {
    pub mod b {
        #[hax_lib::attributes]
        pub trait T {
            #[ensures(|res| res < 10)]
            fn t(&self) -> u32;
        }
    }
}

mod c {
    pub struct S;

    // An impl from another module
    impl super::a::b::T for S {
        fn t(&self) -> u32 {
            0
        }
    }
}

// `impl Trait` argument: an anonymous type parameter with a clause
#[ensures(|res| res < 10)]
fn impl_arg(x: impl a::b::T) -> u32 {
    x.t()
}

struct W<U>(U);

// The clause of the impl is in a `where` clause
impl<U> a::b::T for W<U>
where
    U: a::b::T,
{
    fn t(&self) -> u32 {
        self.0.t()
    }
}
