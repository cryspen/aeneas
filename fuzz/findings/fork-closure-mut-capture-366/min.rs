// A closure that reads through a captured `&mut` reference. Valid Rust.
pub fn read_via_closure(a: &mut u8) -> u8 {
    let read = || -> u8 { *a };
    read()
}
