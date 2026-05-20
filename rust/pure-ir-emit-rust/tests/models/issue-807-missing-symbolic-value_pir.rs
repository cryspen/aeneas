
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

pub struct issue_807_missing_symbolic_value_PortableVector_0 {
    pub elements: [u8; 16usize],
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

pub fn core_iter_traits_iterator_Iterator_next_3<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_156<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_157<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_160<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_163(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_164(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_167(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_171<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_197<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<core_cmp_Ordering_28>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_206<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_209(p0: impl core::marker::Sized) -> usize {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_211(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_2<core_cmp_Ordering_28> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_222(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn issue_807_missing_symbolic_value_to_bytes_0(x: issue_807_missing_symbolic_value_PortableVector_0, bytes: Vec<u8>) -> Result<Vec<u8>> {
    (issue_807_missing_symbolic_value_to_bytes_0_loop0(core_ops_range_Range_1 { start: 0usize, end: 16usize }, x, bytes))
}

pub fn issue_807_missing_symbolic_value_to_bytes_0_loop0(iter: core_ops_range_Range_1<usize>, x: issue_807_missing_symbolic_value_PortableVector_0, bytes: Vec<u8>) -> Result<Vec<u8>> {
    panic!("LoopOp placeholder")
}

