use hax_lib::*;

#[requires(*x < 1000)]
#[ensures(|_| *future(x) == *x + 1 )]
fn incr(x: &mut u32) {
    *x += 1;
}

#[requires(i < x.len() && x[i] < u32::MAX)]
#[ensures(|_| {
        let r = future(x);
        r[i] == x[i] + 1})]
fn incr_i(x: &mut [u32], i: usize) {
    x[i] += 1
}

#[requires(*x < 1000 && *y < 1000)]
// `*x + *y` rather than `x + y`: the latter calls `impl Add<&u32> for &u32`,
// which hax's core models do not define yet.
#[ensures(|r| { *future(y) == *x && *future(x) == *y && r == *x + *y})]
fn swap_and_add(x: &mut u32, y: &mut u32) -> u32 {
    let tmp_x = *x;
    let tmp_y = *y;
    *x = tmp_y;
    *y = tmp_x;
    tmp_x + tmp_y
}

// A shared borrow, read in the postcondition
#[ensures(|result| result == *x)]
fn read_shared(x: &u32) -> u32 {
    *x
}

// A shared borrow next to a mutable one
#[requires(*x < 1000 && *y < 1000)]
#[ensures(|_| *future(x) == *x + *y)]
fn add_assign(x: &mut u32, y: &u32) {
    *x += *y;
}

pub struct Counter {
    pub count: u32,
}

#[hax_lib::attributes]
impl Counter {
    // `&mut self`, and `future(self)` in the postcondition
    #[requires(self.count < 1000)]
    #[ensures(|_| future(self).count == self.count + 1)]
    pub fn bump(&mut self) {
        self.count += 1;
    }
}
