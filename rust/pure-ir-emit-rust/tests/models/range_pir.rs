
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

pub struct core_ops_range_RangeTo_1<Idx> {
    pub end: Idx,
}

pub enum core_option_Option_3<T> {
    None,
    Some(T),
}

pub fn impl_core_slice_index_index_2<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_3<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_3<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_4<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_3<Clause0_Output>, Box<dyn FnOnce(core_option_Option_3<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_5<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_6<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_7<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_8<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_9<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_3<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_10<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_3<Vec<T>>, Box<dyn FnOnce(core_option_Option_3<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_11<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_12<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_13<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_14<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_15<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_3<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_16<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_3<Vec<T>>, Box<dyn FnOnce(core_option_Option_3<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_17<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_18<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_19<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_20<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn range_use_range_0(s: Vec<bool>) -> Result<()> {
    let _: Vec<bool> = (impl_core_slice_index_index_2::<bool, core_ops_range_Range_0<usize>, Vec<bool>>(s, core_ops_range_Range_0 { start: 0usize, end: 1usize }))?;
    Ok(())
}

pub fn range_use_range_to_1(s: Vec<bool>) -> Result<()> {
    let _: Vec<bool> = (impl_core_slice_index_index_2::<bool, core_ops_range_RangeTo_1<usize>, Vec<bool>>(s, core_ops_range_RangeTo_1 { end: 1usize }))?;
    Ok(())
}

