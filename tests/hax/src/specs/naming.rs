// Items with names like the generated `foo.pre`/`foo.post`/`foo.spec`/
// `foo.spec.proof` which don't clash (a clash is an error).
use hax_lib::*;

#[requires(x < 100)]
#[ensures(|result| result == x + 1)]
pub fn foo(x: u32) -> u32 {
    x + 1
}

// Same path as the contracted `foo`, but no clash.
pub mod foo {
    pub fn precondition(x: u32) -> bool {
        x < 100
    }

    pub mod spec {
        pub fn lemma() {}
    }
}

// No clash: not the name of a contracted function.
pub fn proof() {}

pub mod bar {
    pub fn pre() {}
}
