// Two sequential `while let` loops over a mutable-borrow iterator, where the
// FIRST loop early-returns. Valid Rust; rustc accepts it.
pub struct IterMut<'a> {
    v: Option<&'a mut i32>,
}
impl<'a> IterMut<'a> {
    fn next(&mut self) -> Option<&'a mut i32> {
        core::mem::replace(&mut self.v, None)
    }
}
pub fn drain_twice(mut it: IterMut<'_>, stop: bool) {
    while let Some(_) = it.next() {
        if stop {
            return;
        }
    }
    while let Some(_) = it.next() {}
}
