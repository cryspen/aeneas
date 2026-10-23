//@ [lean] known-failure
//@ [!lean] skip
//@ [lean] aeneas-args=-specs hax
//! `-specs hax` requires `-core-models-lib`: the generated specs refer to the
//! `CoreModels` library.

pub fn f() {}
