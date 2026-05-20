
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

pub struct issue_789_loop_ctx_match_S_0 {
    pub x: u8,
    pub y: [u8; 4usize],
}

pub struct core_ops_range_RangeFrom_1<Idx> {
    pub start: Idx,
}

pub enum core_option_Option_3<T> {
    None,
    Some(T),
}

pub fn impl_core_slice_index_index_2<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_is_empty_3<T>(p0: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_4<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_3<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_5<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_3<Clause0_Output>, Box<dyn FnOnce(core_option_Option_3<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_6<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_7<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_8<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_9<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_10<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_3<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_11<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_3<Vec<T>>, Box<dyn FnOnce(core_option_Option_3<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_12<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_13<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_14<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_15<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn issue_789_loop_ctx_match_the_loop_1(s: issue_789_loop_ctx_match_S_0, next_in: Vec<u8>) -> Result<(bool, issue_789_loop_ctx_match_S_0, Vec<u8>)> {
    let (v0, v1, next_in_2, done_3): (u8, [u8; 4usize], Vec<u8>, bool) = (issue_789_loop_ctx_match_the_loop_1_loop0(s, next_in))?;
    Ok((done_3, issue_789_loop_ctx_match_S_0 { x: v0, y: v1 }, next_in_2))
}

pub fn issue_789_loop_ctx_match_f_0(_r: u8, _a: Vec<u8>, _b: Vec<u8>) -> Result<((bool, usize), u8, Vec<u8>)> {
    Ok(((true, 0usize), _r, _b))
}

pub fn issue_789_loop_ctx_match_the_loop_1_loop0(s: issue_789_loop_ctx_match_S_0, next_in: Vec<u8>) -> Result<(u8, [u8; 4usize], Vec<u8>, bool)> {
    panic!("LoopOp placeholder")
}

