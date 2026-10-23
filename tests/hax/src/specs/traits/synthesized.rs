// Annotated traits with one condition per method, no impl: the other
// condition is synthesized as `ok true`. The result type of a synthesized post
// is rewritten into the generics of the decoration fns.

use hax_lib::*;

#[hax_lib::attributes]
trait Gen {
    // Post only: `U` is only in the result, explicit in the synthesized pre
    #[ensures(|_| true)]
    fn pick<U>() -> Option<U>;

    // A method type parameter in the result
    #[requires(true)]
    fn id<U>(&self, u: U) -> U;

    // `&mut self`: the back value is in the result
    #[requires(x < 100)]
    fn add(&mut self, x: u32) -> u32;

    // A const generic in the result
    #[requires(true)]
    fn arr<const N: usize>(&self) -> [u32; N];
}

// A trait type parameter in the result, after `Self_`
#[hax_lib::attributes]
trait Tg<T> {
    #[requires(true)]
    fn get(&self) -> T;
}

// An associated type in the result: `Self_Item` in the trait, `Clause0_Item`
// in the decoration fns
#[hax_lib::attributes]
trait Assoc {
    type Item;

    #[requires(true)]
    fn item(&self) -> Self::Item;
}

trait K {
    fn k() -> u32;
}

// Two clauses on the same trait, `Self_: K` and `U: K`: `U::k()` in the
// precondition is read from the instance of `U`, not from that of `Self`
#[hax_lib::attributes]
trait Sym: K {
    #[requires(x < U::k() && U::k() < 10)]
    fn g<U: K>(x: u32) -> u32;
}

// A method clause whose argument mentions another method type parameter
#[hax_lib::attributes]
trait Nested {
    #[requires(true)]
    fn m<V, U: Tg<Option<V>>>(&self, u: U, v: u32) -> u32;
}

// Many clauses on the same trait, with a supertrait without associated type
#[hax_lib::attributes]
trait Many: Clone {
    #[requires(true)]
    fn m<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone, F: Clone, G: Clone, H: Clone>(
        &self,
    ) -> u32;
}

// BUG: aeneas fails on the conditions of a trait method when the trait or a
// supertrait has an associated type: it maps their generics positionally to
// the method's, but charon lifts the associated type once per clause path
// (`SubAssoc.len.pre {Self_} {Clause0_Item} {Clause1_Clause0_Item}` vs
// `Self, Self_Clause0_Item`) and after the method's own type parameters
// (`AssocGen.f.post {Self_} {U} {Clause0_Item}` vs `Self, Self_Item, U`).
// - `SubAssoc`, `Call`, `SubGen`, `ManyAssoc`, `Sym2`: "Internal error: the
//   generics of the conditions of `…` don't match those of the trait and the
//   method", contract dropped (exit 1);
// - `SubBoth`: "Internal error: the generics of the condition `SubBoth::h.pre`
//   don't match those it is applied to" (exit 2);
// - `AssocGen`: synthesized post with `res : Clause0_Item`, then "Could not
//   find an instance for a trait clause of a pre/post condition" (exit 2).
// The traits are commented out because aeneas fails on them.

// // A supertrait with an associated type. The decoration fns have one copy of
// // the lifted associated type per clause (`Clause0_Item` for `Self_: Assoc`,
// // `Clause1_Clause0_Item` for `Self_: SubAssoc`), the trait only one
// // (`Self_Clause0_Item`). The result does not mention the associated type.
// #[hax_lib::attributes]
// trait SubAssoc: Assoc {
//     #[requires(true)]
//     fn len(&self) -> usize;
// }

// // The same with a generic supertrait, as `FnMut<Args>: FnOnce<Args>`
// #[hax_lib::attributes]
// trait CallOnce<Args> {
//     type Output;
// }
//
// #[hax_lib::attributes]
// trait Call<Args>: CallOnce<Args> {
//     #[requires(true)]
//     fn call(&self, args: Args) -> Self::Output;
// }

// // An associated type and a method type parameter: in the decoration fns, the
// // lifted `Clause0_Item` comes after `U`, in the method after `Self`
// #[hax_lib::attributes]
// trait AssocGen {
//     type Item;
//
//     #[requires(true)]
//     fn f<U>(&self, u: U) -> U;
// }

// // A supertrait with an associated type and a bounded method type parameter:
// // the clause `U: Assoc` of the conditions gets the instance of `U`, not the
// // parent `Self: Assoc`
// #[hax_lib::attributes]
// trait SubGen: Assoc {
//     #[requires(true)]
//     fn g<U: Assoc>(&self, u: U) -> U;
// }

// // Both conditions written, with a supertrait with an associated type
// #[hax_lib::attributes]
// trait SubBoth: Assoc {
//     #[requires(true)]
//     #[ensures(|r| r == 0)]
//     fn h(&self) -> usize;
// }

// // `Many` with a supertrait with an associated type: the conditions get the
// // instances of `A`…`H` in order, and `Self_Clause0_Item` for both lifted
// // copies of the associated type (`Clause8_Item`, `Clause9_Clause0_Item`)
// #[hax_lib::attributes]
// trait ManyAssoc: Assoc {
//     #[requires(true)]
//     fn m<A: Clone, B: Clone, C: Clone, D: Clone, E: Clone, F: Clone, G: Clone, H: Clone>(
//         &self,
//     ) -> u32;
// }

// trait K2 {
//     type X;
//
//     fn k() -> u32;
// }
//
// // `Sym` with an associated type: two clauses on `K2`, `Self_: K2` and
// // `U: K2`; `U::k()` must be read from the instance of `U`
// #[hax_lib::attributes]
// trait Sym2: K2 {
//     #[requires(x < U::k() && U::k() < 10)]
//     fn g<U: K2>(x: u32) -> u32;
// }
