
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

pub struct core_ops_range_Range_0<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub enum core_option_Option_1<T> {
    None,
    Some(T),
}

pub enum core_cmp_Ordering_27 {
    Less,
    Equal,
    Greater,
}

pub fn impl_core_iter_range_next_33<A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_1<A>, core_ops_range_Range_0<A>)> where A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_num_wrapping_sub_34(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn impl_core_num_wrapping_add_35(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_36<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_1<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_189<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_1<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_190<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_193<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_196(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_1<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_197(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<usize>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_200(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<usize>> {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_204<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_230<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<core_cmp_Ordering_27>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_239<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_242(p0: impl core::marker::Sized) -> usize {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_244(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_1<core_cmp_Ordering_27> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_255(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn assert_cfg_assert_or_in_loop_31(a: [u32; 10usize]) -> Result<[u32; 10usize]> {
    (assert_cfg_assert_or_in_loop_31_loop0(core_ops_range_Range_0 { start: 0usize, end: 10usize }, a))
}

pub fn assert_cfg_assert_in_loop_30(a: [u32; 10usize]) -> Result<()> {
    (assert_cfg_assert_in_loop_30_loop0(core_ops_range_Range_0 { start: 0usize, end: 10usize }, a))
}

pub fn assert_cfg_assert_arith_29(x: u32, y: u32) -> Result<()> {
    let v0: u32 = (x.checked_add(y).ok_or(()))?;
    let _: () = (if (v0 < 100u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_lt_23(x: u32) -> Result<()> {
    let _: () = (if (x < 10u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_le_24(x: u32) -> Result<()> {
    let _: () = (if (x <= 3494u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_gt_25(x: u32) -> Result<()> {
    let _: () = (if (x > 0u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_ge_26(x: u32) -> Result<()> {
    let _: () = (if (x >= 1u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_eq_27(x: u32) -> Result<()> {
    let _: () = (if (x == 42u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_ne_28(x: u32) -> Result<()> {
    let _: () = (if (x != 0u32) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_or_3(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if (b0 || b1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_and_6(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if ((!b0) || (!b1)) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_or_b1_7(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if ((!b0) || b1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_b0_or_not_b1_8(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if (b0 || (!b1)) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_or_not_b1_9(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if ((!b0) || (!b1)) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_or_call_13() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { Ok(()) } else { {
    let v1: bool = (assert_cfg_get_b1_1())?;
    (if v1 { Ok(()) } else { Err(()) })
} })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_and_call_16() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { {
    let v1: bool = (assert_cfg_get_b1_1())?;
    (if (!v1) { Ok(()) } else { Err(()) })
} } else { Ok(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_or_b1_call_17() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { {
    let v1: bool = (assert_cfg_get_b1_1())?;
    (if v1 { Ok(()) } else { Err(()) })
} } else { Ok(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_b0_or_not_b1_call_18() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { Ok(()) } else { {
    let v1: bool = (assert_cfg_get_b1_1())?;
    (if (!v1) { Ok(()) } else { Err(()) })
} })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_or_not_b1_call_19() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { {
    let v1: bool = (assert_cfg_get_b1_1())?;
    (if (!v1) { Ok(()) } else { Err(()) })
} } else { Ok(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_and_4(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if b0 { Ok(()) } else { Err(()) })?;
    let _: () = (if b1 { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_or_5(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if (!b0) { Ok(()) } else { Err(()) })?;
    let _: () = (if (!b1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_and_b1_10(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if (!b0) { Ok(()) } else { Err(()) })?;
    let _: () = (if b1 { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_b0_and_not_b1_11(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if b0 { Ok(()) } else { Err(()) })?;
    let _: () = (if (!b1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_and_not_b1_12(b0: bool, b1: bool) -> Result<()> {
    let _: () = (if (!b0) { Ok(()) } else { Err(()) })?;
    let _: () = (if (!b1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_and_call_14() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { Ok(()) } else { Err(()) })?;
    let v1: bool = (assert_cfg_get_b1_1())?;
    let _: () = (if v1 { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_or_call_15() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if (!v0) { Ok(()) } else { Err(()) })?;
    let v1: bool = (assert_cfg_get_b1_1())?;
    let _: () = (if (!v1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_and_b1_call_20() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if (!v0) { Ok(()) } else { Err(()) })?;
    let v1: bool = (assert_cfg_get_b1_1())?;
    let _: () = (if v1 { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_b0_and_not_b1_call_21() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if v0 { Ok(()) } else { Err(()) })?;
    let v1: bool = (assert_cfg_get_b1_1())?;
    let _: () = (if (!v1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_assert_not_b0_and_not_b1_call_22() -> Result<()> {
    let v0: bool = (assert_cfg_get_b0_0())?;
    let _: () = (if (!v0) { Ok(()) } else { Err(()) })?;
    let v1: bool = (assert_cfg_get_b1_1())?;
    let _: () = (if (!v1) { Ok(()) } else { Err(()) })?;
    (assert_cfg_f_2())
}

pub fn assert_cfg_f_2() -> Result<()> {
    Ok(())
}

pub fn assert_cfg_get_b0_0() -> Result<bool> {
    Ok(true)
}

pub fn assert_cfg_get_b1_1() -> Result<bool> {
    Ok(true)
}

pub fn assert_cfg_assert_or_in_loop_31_loop0(iter: core_ops_range_Range_0<usize>, a: [u32; 10usize]) -> Result<[u32; 10usize]> {
    panic!("LoopOp placeholder")
}

pub fn assert_cfg_assert_in_loop_30_loop0(iter: core_ops_range_Range_0<usize>, a: [u32; 10usize]) -> Result<()> {
    panic!("LoopOp placeholder")
}

