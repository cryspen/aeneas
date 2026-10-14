// A trait with a generic parameter, a concrete impl and a generic caller.

use hax_lib::*;

#[hax_lib::attributes]
trait Conv<T> {
    #[ensures(|res| res < 10)]
    fn conv(&self, t: T) -> u32;
}

impl Conv<u8> for u32 {
    fn conv(&self, _t: u8) -> u32 {
        0
    }
}

#[ensures(|res| res < 10)]
fn use_conv<C: Conv<u8>>(c: &C) -> u32 {
    c.conv(0)
}
