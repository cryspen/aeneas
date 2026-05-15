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

/// M11 fixture: in-body if-then-else with a join (no early return),
/// so the cert exercises `EvJoin` + branch-marker [EvAssert] pairs.
///
/// The post-`if` `r + 1` ensures both branches fall through to a
/// shared continuation rather than emitting a per-branch tail return,
/// which is what triggers [eval_switch_with_join] to actually fire.
pub fn pick(b: bool, x: u32, y: u32) -> u32 {
    let mut r = 0u32;
    if b {
        r = x;
    } else {
        r = y;
    }
    r.wrapping_add(1)
}
