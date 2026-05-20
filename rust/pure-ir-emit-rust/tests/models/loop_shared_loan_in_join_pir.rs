
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

pub struct loop_shared_loan_in_join_State_0 {
    pub data: [u64; 4usize],
    pub index: u32,
    pub limit: u32,
    pub padding: u8,
    pub flag: bool,
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

pub fn impl_core_iter_range_next_2<A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<A>, core_ops_range_Range_1<A>)> where A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_num_wrapping_add_3(p0: u64, p1: u64) -> u64 {
    // route: core_models::num::*::wrapping_add → rust_primitives::arithmetic::wrapping_add_<t>
    u64::wrapping_add(p0, p1)
}

pub fn core_iter_traits_iterator_Iterator_next_5<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_158<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_159<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_162<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_165(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_166(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_169(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_173<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_199<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<core_cmp_Ordering_28>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_208<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_211(p0: impl core::marker::Sized) -> usize {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_213(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_2<core_cmp_Ordering_28> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_224(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn impl_loop_shared_loan_in_join_extract_4(self_: loop_shared_loan_in_join_State_0, result: Vec<u64>, count: usize) -> Result<(loop_shared_loan_in_join_State_0, Vec<u64>)> {
    let lane_index_0: usize = Ok((self_.index as usize))?;
    let (v1, v2, result_3): ([u64; 4usize], u32, Vec<u64>) = (impl_loop_shared_loan_in_join_extract_4_loop0(core_ops_range_Range_1 { start: 0usize, end: count }, self_.data, self_.index, self_.limit, result, lane_index_0))?;
    Ok((loop_shared_loan_in_join_State_0 { data: v1, index: v2, limit: self_.limit, padding: self_.padding, flag: self_.flag }, result_3))
}

pub fn loop_shared_loan_in_join_transform_0(data: [u64; 4usize]) -> Result<[u64; 4usize]> {
    (loop_shared_loan_in_join_transform_0_loop0(core_ops_range_Range_1 { start: 0usize, end: 4usize }, data))
}

pub fn impl_loop_shared_loan_in_join_extract_4_loop0(iter: core_ops_range_Range_1<usize>, p1: [u64; 4usize], p2: u32, p3: u32, result: Vec<u64>, lane_index: usize) -> Result<([u64; 4usize], u32, Vec<u64>)> {
    panic!("LoopOp placeholder")
}

pub fn loop_shared_loan_in_join_transform_0_loop0(iter: core_ops_range_Range_1<usize>, data: [u64; 4usize]) -> Result<[u64; 4usize]> {
    panic!("LoopOp placeholder")
}

