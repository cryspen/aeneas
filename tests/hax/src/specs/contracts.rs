use hax_lib::*;

#[requires(x < 100)]
fn only_requires(x: u32) -> u32 {
    x + 1
}

#[ensures(|result| result == x)]
fn only_ensures(x: u32) -> u32 {
    x
}

#[requires(x < 10)]
#[ensures(|result| result > x)]
fn both(x: u32) -> u32 {
    x + 1
}

// No arguments
#[ensures(|_| true)]
fn no_args() {
    let _x = 0;
    ()
}

// Unit return with a by-value argument
#[requires(x < 10)]
#[ensures(|_| true)]
fn returns_unit(x: u32) {}

// Block expression (with a `let`) inside `requires`
#[requires({ let bound = x; bound > 10 })]
fn block_in_requires(x: u32) -> u32 {
    x
}

// Pattern directly in the result closure
#[ensures(|(a, b)| a == x && b == x)]
fn returns_pair(x: u32) -> (u32, u32) {
    (x, x)
}
