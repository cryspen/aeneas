
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

pub struct core_ops_range_RangeFrom_0<Idx> {
    pub start: Idx,
}

pub enum core_option_Option_1<T> {
    None,
    Some(T),
}

pub struct core_ops_range_Range_2<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub fn impl_core_slice_index_index_6<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_get_7<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Clause0_Output>> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_8<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> Vec<T>>)> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_get_mut_9<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_1<Clause0_Output>, Box<dyn FnOnce(core_option_Option_1<Clause0_Output>) -> Vec<T>>)> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_10<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_11<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_1<Clause0_Output>, Box<dyn FnOnce(core_option_Option_1<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_12<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_13<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_14<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_15<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_16<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_17<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_1<Vec<T>>, Box<dyn FnOnce(core_option_Option_1<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_18<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_19<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_20<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_21<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_22<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_1<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_23<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_1<Vec<T>>, Box<dyn FnOnce(core_option_Option_1<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_24<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_25<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_26<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_27<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn array_slice_index_slice_use_index_mut_range_from_4(s: Vec<u32>) -> Result<(Vec<u32>, Box<dyn FnOnce(Vec<u32>) -> Vec<u32>>)> {
    (impl_core_slice_index_index_mut_8::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(s, core_ops_range_RangeFrom_0 { start: 0usize }))
}

pub fn array_slice_index_slice_use_index_range_from_0(s: Vec<u32>) -> Result<Vec<u32>> {
    (impl_core_slice_index_index_6::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(s, core_ops_range_RangeFrom_0 { start: 0usize }))
}

pub fn array_slice_index_slice_use_index_range_2(s: Vec<u32>) -> Result<Vec<u32>> {
    (impl_core_slice_index_index_6::<u32, core_ops_range_Range_2<usize>, Vec<u32>>(s, core_ops_range_Range_2 { start: 0usize, end: 1usize }))
}

pub fn array_slice_index_slice_use_get_range_from_1(s: Vec<u32>) -> Result<core_option_Option_1<Vec<u32>>> {
    (impl_core_slice_get_7::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(s, core_ops_range_RangeFrom_0 { start: 0usize }))
}

pub fn array_slice_index_slice_use_get_range_3(s: Vec<u32>) -> Result<core_option_Option_1<Vec<u32>>> {
    (impl_core_slice_get_7::<u32, core_ops_range_Range_2<usize>, Vec<u32>>(s, core_ops_range_Range_2 { start: 0usize, end: 1usize }))
}

pub fn array_slice_index_slice_use_get_mut_range_from_5(s: Vec<u32>) -> Result<(core_option_Option_1<Vec<u32>>, Box<dyn FnOnce(core_option_Option_1<Vec<u32>>) -> Vec<u32>>)> {
    (impl_core_slice_get_mut_9::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(s, core_ops_range_RangeFrom_0 { start: 0usize }))
}

