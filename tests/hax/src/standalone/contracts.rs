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

// Unit return with a by-value argument
#[requires(x < 10)]
#[ensures(|_| true)]
fn returns_unit(x: u32) {}

// No arguments
#[ensures(|_| true)]
fn no_args() {
    let _x = 0;
    ()
}

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

// `Option` result, inspected with a `match` in the postcondition
#[ensures(|result| match result { Some(v) => v == x, None => false })]
fn returns_option(x: u32) -> Option<u32> {
    Some(x)
}

// `Result` result
#[requires(x < 100)]
#[ensures(|result| match result { Ok(v) => v == x + 1, Err(_) => false })]
fn returns_result(x: u32) -> Result<u32, ()> {
    Ok(x + 1)
}

// A body which can panic (division by zero), unless the precondition holds
#[requires(y != 0)]
#[ensures(|result| result <= x)]
fn may_panic(x: u32, y: u32) -> u32 {
    x / y
}

// An explicit panic, which the precondition makes unreachable
#[requires(x < 10)]
#[ensures(|result| result == x)]
fn explicit_panic(x: u32) -> u32 {
    if x >= 10 {
        panic!()
    }
    x
}
