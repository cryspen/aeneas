
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

pub struct loops_issues_WrapperU32_0 {
    pub x: u32,
}

pub struct core_ops_range_Range_1<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub enum core_option_Option_2<T> {
    None,
    Some(T),
}

pub enum core_cmp_Ordering_28 {
    Less,
    Equal,
    Greater,
}

pub fn impl_core_slice_len_11<T>(p0: impl core::marker::Sized) -> usize where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_next_14<A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<A>, core_ops_range_Range_1<A>)> where A: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_15<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_168<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_169<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_172<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_175(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_176(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<i32>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_179(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<i32>> {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_183<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_209<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<core_cmp_Ordering_28>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_218<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_221(p0: impl core::marker::Sized) -> i32 {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_223(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_2<core_cmp_Ordering_28> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_234(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn loops_issues_test_7(b0: bool, b1: bool) -> Result<()> {
    let buf_0: [u8; 4usize] = unimplemented!("placeholder");
    (loops_issues_test_7_loop0(b0, b1, buf_0))
}

pub fn loops_issues_mut_loop_len_6(p0: u32, b: bool) -> Result<u32> {
    let buf_0: [u8; 4usize] = unimplemented!("placeholder");
    let _: () = (loops_issues_mut_loop_len_6_loop0(b, buf_0))?;
    Ok(p0)
}

pub fn loops_issues_loop_array_len_write_4(b0: bool, b1: bool) -> Result<()> {
    let buf_0: [u8; 4usize] = unimplemented!("placeholder");
    (loops_issues_loop_array_len_write_4_loop0(b0, b1, buf_0))
}

pub fn loops_issues_loop_consume_u32_9(params: loops_issues_WrapperU32_0) -> Result<()> {
    (loops_issues_loop_consume_u32_9_loop0(params, core_ops_range_Range_1 { start: 0i32, end: 32i32 }))
}

pub fn loops_issues_loop_access_array_2(k: usize) -> Result<()> {
    (loops_issues_loop_access_array_2_loop0(k, 0usize))
}

pub fn loops_issues_read_global_loop_5(b: bool, n_rows: usize) -> Result<()> {
    let _: () = (if (n_rows <= 0usize) { Ok(()) } else { Err(()) })?;
    (loops_issues_read_global_loop_5_loop0(b))
}

pub fn loops_issues_loop_array_len_3(b: bool) -> Result<()> {
    (loops_issues_loop_array_len_3_loop0(b))
}

pub fn loops_issues_write_0(p0: [u8; 4usize]) -> Result<[u8; 4usize]> {
    Ok(p0)
}

pub fn loops_issues_read_1(p0: [u8; 4usize]) -> Result<()> {
    Ok(())
}

pub fn loops_issues_consume_u32_8(eta: u32) -> Result<()> {
    Ok(())
}

pub fn loops_issues_CARRAY_10() -> [u16; 4usize] {
    unimplemented!("FBuiltin call")
}

pub fn loops_issues_MAX_NROWS_12() -> usize {
    4usize
}

pub fn loops_issues_test_7_loop0(b0: bool, b1: bool, buf: [u8; 4usize]) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_mut_loop_len_6_loop0(b: bool, buf: [u8; 4usize]) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_loop_array_len_write_4_loop0(b0: bool, b1: bool, buf: [u8; 4usize]) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_loop_consume_u32_9_loop0(params: loops_issues_WrapperU32_0, iter: core_ops_range_Range_1<i32>) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_loop_access_array_2_loop0(k: usize, start: usize) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_read_global_loop_5_loop0(b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_issues_loop_array_len_3_loop0(b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

