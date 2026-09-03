// Minimal reproducer: two consecutive `assert!` of the SAME boolean local
// crashes Aeneas translation with "There should be no bottoms in the value".
// Valid Rust (rustc accepts it, including with -C overflow-checks=on).
pub fn f(b0: bool) {
    assert!(b0);
    assert!(b0);
}
