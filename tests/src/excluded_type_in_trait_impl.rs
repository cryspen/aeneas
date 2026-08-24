//@ [!lean] skip
//@ [lean] known-failure
//@ charon-args=--exclude excluded_type_in_trait_impl::Excluded
// A trait implementation whose implemented trait mentions a type that is
// *excluded* from the crate (here via Charon's `--exclude`). Deriving the
// extraction name for the impl resolves the trait's generic arguments to name
// patterns through the Charon name-matcher, which does a raw `Map.find` on the
// type declarations. Because `Excluded` was removed, that lookup raised a raw
// `Not_found`.
//
// Regression: this previously aborted the translation of the *whole crate* with
// an uncaught `Not_found` (the exception escaped the `CFailure` containment of
// the name-registration loops in `extract_translated_crate`). It is now
// contained at item granularity: `ctx_compute_trait_impl_name_raw` routes the
// failure through `[%craise]`, naming the offending trait implementation.
// Without `-abort-on-error` the impl (and its method) are skipped with a
// warning and the rest of the crate still translates; with `-abort-on-error`
// (as this test runs) the failure is reported as a clean hard error, below.

pub struct Excluded {
    pub v: u32,
}

pub trait MyTrait<T> {
    fn f(&self) -> u32;
}

pub struct Holder;

impl MyTrait<Excluded> for Holder {
    fn f(&self) -> u32 {
        0
    }
}

pub fn main() {}
