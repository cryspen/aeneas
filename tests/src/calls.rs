//! M10.2 fixtures: functions that *call* `&mut`-taking helpers so the
//! cert exercises the End-Abstraction event.

pub fn incr_inner(y: &mut u32) {
    *y += 1;
}

pub fn incr_via_helper(x: &mut u32) {
    incr_inner(x);
}

pub fn choose<'a>(b: bool, x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 {
    if b { x } else { y }
}

pub fn use_choose(b: bool, x: &mut u32, y: &mut u32) {
    let r = choose(b, x, y);
    *r = 7;
}
