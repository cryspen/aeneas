//@ [!lean] skip
// An enum with a discriminant that does not fit in an OCaml integer.

#[repr(u128)]
pub enum HugeDiscriminant {
    Small = 0,
    Huge = u128::MAX,
}
