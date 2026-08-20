//@ [!lean] skip
//@ [lean] known-failure
// A trait with a *generic associated type* (GAT) used in a method signature
// (`owned_to_ref(&self) -> Self::Borrowed<'_>`). Aeneas erases regions and
// cannot model associated types that take their own generic parameters, so the
// method signature fails to translate.
//
// Regression: this previously aborted the translation of the *whole crate* with
// an uncaught exception (the failure escaped item-level containment in
// `translate_method_sig`). It is now contained at item granularity: without
// `-abort-on-error` the trait/impl are skipped with a warning and the rest of
// the crate still translates. With `-abort-on-error` (as this test runs) the
// failure is reported as a hard error, below.

pub trait OwnedToRef {
    type Borrowed<'a>
    where
        Self: 'a;

    fn owned_to_ref(&self) -> Self::Borrowed<'_>;
}

impl<T> OwnedToRef for Option<T>
where
    T: OwnedToRef,
{
    type Borrowed<'a>
        = Option<T::Borrowed<'a>>
    where
        T: 'a;

    fn owned_to_ref(&self) -> Self::Borrowed<'_> {
        self.as_ref().map(|o| o.owned_to_ref())
    }
}
