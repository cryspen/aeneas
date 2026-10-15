//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods -external-names tests/external-names/external-names-traits.json -extra-includes=ExternalNamesModel
//! A trait modelled through a list of external names, whose model declares only
//! some of the trait's methods: with `-filter-trait-methods`, the extracted impls
//! only provide the modelled methods (here, `write_str` but not the provided
//! `write_char` and `write_fmt`).

pub struct Counter {
    pub n: usize,
}

impl core::fmt::Write for Counter {
    fn write_str(&mut self, _s: &str) -> core::fmt::Result {
        self.n = self.n.wrapping_add(1);
        Ok(())
    }
}
