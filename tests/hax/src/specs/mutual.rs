// The decoration items hax adds for the specs of mutually recursive functions
// are removed by the late-skip prepass even inside a recursive group.
use hax_lib::*;

#[requires(n < 1000)]
#[ensures(|result| result == (n % 2 == 0))]
fn is_even(n: u32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

#[requires(n < 1000)]
#[ensures(|result| result == (n % 2 == 1))]
fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}
