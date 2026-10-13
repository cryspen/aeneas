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

// `hax_lib::Prop` connectives: `implies` in both conditions
#[requires(implies(x >= 10, y == 0))]
#[ensures(|result| implies(x >= 10, result == x))]
fn implies_cond(x: u32, y: u32) -> u32 {
    if x >= 10 {
        x + y
    } else {
        x
    }
}

// `forall` in the precondition, `exists` in the postcondition
#[requires(forall(|i: u32| implies(i < x, i < 100)))]
#[ensures(|result| exists(|i: u32| result == i))]
fn quantifiers(x: u32) -> u32 {
    x
}

// Mathematical integers, the usual way to state that an operation does not
// overflow
#[requires(x.to_int() + y.to_int() <= u32::MAX.to_int())]
#[ensures(|result| result.to_int() == x.to_int() + y.to_int())]
fn int_bounds(x: u32, y: u32) -> u32 {
    x + y
}

fn is_small(x: u32) -> bool {
    x < 100
}

// A condition calling a helper function
#[requires(is_small(x))]
#[ensures(|result| result == x + 1)]
fn helper_in_requires(x: u32) -> u32 {
    x + 1
}

// A condition calling a function which has a contract itself
#[requires(x < 10)]
#[ensures(|result| result == both(x) + 1)]
fn calls_contracted(x: u32) -> u32 {
    both(x) + 1
}

// A recursive function
#[requires(n < 100)]
#[ensures(|result| result == n)]
fn recursive(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        recursive(n - 1) + 1
    }
}

// A loop. (Without `loop_invariant!`, which hax's Lean library does not model
// yet.)
#[requires(n < 100)]
#[ensures(|result| result == n)]
fn with_loop(n: u32) -> u32 {
    let mut acc = 0;
    for i in 0..n {
        acc += 1;
    }
    acc
}
