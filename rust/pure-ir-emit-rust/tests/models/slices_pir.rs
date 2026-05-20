
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

// TODO: opaque type alloc_vec_Vec_1 — emitting marker struct.
pub struct alloc_vec_Vec_1<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_2;

pub enum core_option_Option_4<T> {
    None,
    Some(T),
}

pub fn impl_core_slice_index_index_6<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_7<T, I, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> Vec<T>>)> where T: 'static, I: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_split_at_8<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Vec<T>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_split_at_mut_9<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<((Vec<T>, Vec<T>), Box<dyn FnOnce((Vec<T>, Vec<T>)) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_swap_10<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized, p2: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_from_11<T, A>(p0: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_13<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_4<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_14<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_4<Clause0_Output>, Box<dyn FnOnce(core_option_Option_4<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_15<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_16<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_17<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_18<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_19<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_4<Vec<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_20<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_4<Vec<T>>, Box<dyn FnOnce(core_option_Option_4<Vec<T>>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_21<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_22<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_23<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_24<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn slices_slice_subslice_from_mut_1(x: Vec<u32>) -> Result<(Vec<u32>, Box<dyn FnOnce(Vec<u32>) -> Vec<u32>>)> {
    (impl_core_slice_index_index_mut_7::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(x, core_ops_range_RangeFrom_0 { start: 0usize }))
}

pub fn slices_slice_subslice_from_shared_0(x: Vec<u32>) -> Result<Vec<u32>> {
    (impl_core_slice_index_index_6::<u32, core_ops_range_RangeFrom_0<usize>, Vec<u32>>(x, core_ops_range_RangeFrom_0 { start: 0usize }))
}

pub fn slices_swap_4<T>(x: Vec<T>, n: usize, m: usize) -> Result<Vec<T>> where T: 'static {
    (impl_core_slice_swap_10::<T>(x, n, m))
}

pub fn slices_split_at_2<T>(x: Vec<T>, n: usize) -> Result<(Vec<T>, Vec<T>)> where T: 'static {
    (impl_core_slice_split_at_8::<T>(x, n))
}

pub fn slices_split_at_mut_3<T>(x: Vec<T>, n: usize) -> Result<((Vec<T>, Vec<T>), Box<dyn FnOnce((Vec<T>, Vec<T>)) -> Vec<T>>)> where T: 'static {
    let (v0, split_at_mut_back_1): ((Vec<T>, Vec<T>), Box<dyn FnOnce((Vec<T>, Vec<T>)) -> Vec<T>>) = (impl_core_slice_split_at_mut_9::<T>(x, n))?;
    let back_2: Box<dyn FnOnce((Vec<T>, Vec<T>)) -> Vec<T>> = (Box::new(move |v3: (Vec<T>, Vec<T>)| -> Vec<T> { (split_at_mut_back_1(v3)) }) as Box<dyn FnOnce((Vec<T>, Vec<T>)) -> Vec<T>>);
    Ok((v0, back_2))
}

pub fn slices_from_vec_5<T>(x: alloc_vec_Vec_1<T>) -> Result<Vec<T>> where T: 'static {
    (impl_alloc_vec_from_11::<T, alloc_alloc_Global_2>(x))
}

