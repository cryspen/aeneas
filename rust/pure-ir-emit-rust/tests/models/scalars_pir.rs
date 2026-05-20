
pub mod aeneas_runtime {
    /// Aeneas pure-IR runtime shim: Result encodes the `can_fail`
    /// monad threaded by symbolic-to-pure. The unit error keeps the
    /// emitted code minimal; downstream models can refine.
    pub type Result<T> = core::result::Result<T, ()>;

    #[inline] pub fn ret<T>(x: T) -> Result<T> { Ok(x) }
    #[inline] pub fn fail<T>() -> Result<T> { Err(()) }

    /// Stub `LoopOp`: the IR's loop fixed-point combinator. At the
    /// Rust level we only need a placeholder with the right type
    /// shape so the surrounding code typechecks; the real semantics
    /// live in the Lean translation. The body and init types are
    /// independent of the return type so the same shim accepts the
    /// variety of (input-tuple ↦ break-value) shapes the IR
    /// generates from different loop forms.
    #[inline] pub fn loop_op<T, U, R, F: FnOnce(T) -> Result<U>>(_body: F, _init: T) -> R {
        panic!("loop_op placeholder")
    }

    /// Typed placeholder used wherever the emitter can't faithfully
    /// recover a concrete expression (trait-method dispatch,
    /// builtin calls, opaque globals, etc). Returns `Result<T>` so
    /// the surrounding `?` operator typechecks.
    #[inline] pub fn todo_result<T>(_what: &'static str) -> Result<T> { Err(()) }

    /// Typed placeholder for non-monadic positions.
    #[inline] pub fn todo_value<T>(what: &'static str) -> T { panic!("todo_value: {what}") }
}

use self::aeneas_runtime::Result;

pub fn impl_core_num_wrapping_add_23(p0: u32, p1: u32) -> u32 {
    // route: core_models::num::*::wrapping_add → rust_primitives::arithmetic::wrapping_add_<t>
    u32::wrapping_add(p0, p1)
}

pub fn impl_core_num_wrapping_add_24(p0: i32, p1: i32) -> i32 {
    // route: core_models::num::*::wrapping_add → rust_primitives::arithmetic::wrapping_add_<t>
    i32::wrapping_add(p0, p1)
}

pub fn impl_core_num_wrapping_sub_25(p0: u32, p1: u32) -> u32 {
    // route: core_models::num::*::wrapping_sub → rust_primitives::arithmetic::wrapping_sub_<t>
    u32::wrapping_sub(p0, p1)
}

pub fn impl_core_num_wrapping_sub_26(p0: i32, p1: i32) -> i32 {
    // route: core_models::num::*::wrapping_sub → rust_primitives::arithmetic::wrapping_sub_<t>
    i32::wrapping_sub(p0, p1)
}

pub fn impl_core_num_rotate_right_27(p0: u32, p1: u32) -> u32 {
    // route: core_models::num::*::rotate_right → rust_primitives::arithmetic::rotate_right_<t>
    u32::rotate_right(p0, p1)
}

pub fn impl_core_num_rotate_right_28(p0: i32, p1: u32) -> i32 {
    // route: core_models::num::*::rotate_right → rust_primitives::arithmetic::rotate_right_<t>
    i32::rotate_right(p0, p1)
}

pub fn impl_core_num_rotate_left_29(p0: u32, p1: u32) -> u32 {
    // route: core_models::num::*::rotate_left → rust_primitives::arithmetic::rotate_left_<t>
    u32::rotate_left(p0, p1)
}

pub fn impl_core_num_rotate_left_30(p0: i32, p1: u32) -> i32 {
    // route: core_models::num::*::rotate_left → rust_primitives::arithmetic::rotate_left_<t>
    i32::rotate_left(p0, p1)
}

pub fn impl_core_default_default_31() -> u32 {
    // route: core_models::default::Default::default → Default::default()
    <u32 as core::default::Default>::default()
}

pub fn impl_core_default_default_32() -> i32 {
    // route: core_models::default::Default::default → Default::default()
    <i32 as core::default::Default>::default()
}

pub fn impl_core_num_BITS_33() -> Result<u32> {
    // route: core_models::num::*::BITS → <ret_ty>::BITS (native)
    Ok(u32::BITS)
}

pub fn impl_core_num_BITS_34() -> Result<u32> {
    // route: core_models::num::*::BITS → <ret_ty>::BITS (native)
    Ok(u32::BITS)
}

pub fn scalars_add_and_8(a: u32, b: u32) -> Result<u32> {
    let v0: u32 = Ok((b & a))?;
    let v1: u32 = Ok((b & a))?;
    (v0.checked_add(v1).ok_or(()))
}

pub fn scalars_match_isize_16(x: isize) -> Result<isize> {
    match (x as _) {
    0i128 => Ok(0isize),
    -1i128 => Ok(0isize),
    2i128 => Ok(0isize),
    _ => (x.checked_add(1isize).ok_or(())),
}
}

pub fn scalars_match_usize_15(x: usize) -> Result<bool> {
    match (x as _) {
    0i128 => Ok(true),
    1i128 => Ok(true),
    2i128 => Ok(true),
    _ => Ok(false),
}
}

pub fn scalars_u32_use_wrapping_add_0(x: u32, y: u32) -> Result<u32> {
    Ok((impl_core_num_wrapping_add_23(x, y)))
}

pub fn scalars_i32_use_wrapping_add_1(x: i32, y: i32) -> Result<i32> {
    Ok((impl_core_num_wrapping_add_24(x, y)))
}

pub fn scalars_u32_use_wrapping_sub_2(x: u32, y: u32) -> Result<u32> {
    Ok((impl_core_num_wrapping_sub_25(x, y)))
}

pub fn scalars_i32_use_wrapping_sub_3(x: i32, y: i32) -> Result<i32> {
    Ok((impl_core_num_wrapping_sub_26(x, y)))
}

pub fn scalars_u32_use_shift_right_4(x: u32) -> Result<u32> {
    (x.checked_shr((2i32) as u32).ok_or(()))
}

pub fn scalars_i32_use_shift_right_5(x: i32) -> Result<i32> {
    (x.checked_shr((2i32) as u32).ok_or(()))
}

pub fn scalars_u32_use_shift_left_6(x: u32) -> Result<u32> {
    (x.checked_shl((2i32) as u32).ok_or(()))
}

pub fn scalars_i32_use_shift_left_7(x: i32) -> Result<i32> {
    (x.checked_shl((2i32) as u32).ok_or(()))
}

pub fn scalars_u32_use_rotate_right_9(x: u32) -> Result<u32> {
    Ok((impl_core_num_rotate_right_27(x, 2u32)))
}

pub fn scalars_i32_use_rotate_right_10(x: i32) -> Result<i32> {
    Ok((impl_core_num_rotate_right_28(x, 2u32)))
}

pub fn scalars_u32_use_rotate_left_11(x: u32) -> Result<u32> {
    Ok((impl_core_num_rotate_left_29(x, 2u32)))
}

pub fn scalars_i32_use_rotate_left_12(x: i32) -> Result<i32> {
    Ok((impl_core_num_rotate_left_30(x, 2u32)))
}

pub fn scalars_u32_as_u16_17(x: u32) -> Result<u16> {
    Ok((x as u16))
}

pub fn scalars_u16_as_u32_18(x: u16) -> Result<u32> {
    Ok((x as u32))
}

pub fn scalars_u32_as_i16_19(x: u32) -> Result<i16> {
    Ok((x as i16))
}

pub fn scalars_i16_as_u32_20(x: i16) -> Result<u32> {
    Ok((x as u32))
}

pub fn scalars_u32_use_bits_21() -> Result<u32> {
    Ok(0u32)
}

pub fn scalars_i32_use_bits_22() -> Result<u32> {
    Ok(0u32)
}

pub fn scalars_u32_default_13() -> Result<u32> {
    Ok((impl_core_default_default_31()))
}

pub fn scalars_i32_default_14() -> Result<i32> {
    Ok((impl_core_default_default_32()))
}

