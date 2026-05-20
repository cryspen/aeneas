
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

pub struct iterators_Key_0([u128; 128usize]);

pub struct core_ops_range_Range_1<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub enum core_option_Option_2<T> {
    None,
    Some(T),
}

// TODO: opaque type core_iter_adapters_step_by_StepBy_3 — emitting marker struct.
pub struct core_iter_adapters_step_by_StepBy_3<I>(pub core::marker::PhantomData<fn() -> (I,)>);

// TODO: opaque type core_slice_iter_IterMut_4 — emitting marker struct.
pub struct core_slice_iter_IterMut_4<T>(pub core::marker::PhantomData<fn() -> (T,)>);

// TODO: opaque type core_slice_iter_Iter_5 — emitting marker struct.
pub struct core_slice_iter_Iter_5<T>(pub core::marker::PhantomData<fn() -> (T,)>);

// TODO: opaque type core_slice_iter_ChunksExact_6 — emitting marker struct.
pub struct core_slice_iter_ChunksExact_6<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub enum core_cmp_Ordering_31 {
    Less,
    Equal,
    Greater,
}

pub fn impl_core_iter_range_next_10<A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<A>, core_ops_range_Range_1<A>)> where A: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_step_by_11<Self_, Clause0_Item>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_3<Self_>> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_adapters_step_by_next_12<I, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, core_iter_adapters_step_by_StepBy_3<I>)> where I: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_mut_13<T>(p0: impl core::marker::Sized) -> Result<(core_slice_iter_IterMut_4<T>, Box<dyn FnOnce(core_slice_iter_IterMut_4<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_next_14<T>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<T>, core_slice_iter_IterMut_4<T>, Box<dyn FnOnce(core_slice_iter_IterMut_4<T>) -> Box<dyn FnOnce(core_option_Option_2<T>) -> core_slice_iter_IterMut_4<T>>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_15<T>(p0: impl core::marker::Sized) -> Result<core_slice_iter_Iter_5<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_next_16<T>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<T>, core_slice_iter_Iter_5<T>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_chunks_exact_17<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_slice_iter_ChunksExact_6<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_next_18<T>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Vec<T>>, core_slice_iter_ChunksExact_6<T>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_19<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_step_by_101<A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_3<core_ops_range_Range_1<A>>> where A: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_171<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_172<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_175<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_178(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_2<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_179(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_182(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<usize>> {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_490<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_516<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_2<core_cmp_Ordering_31>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_525<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_528(p0: impl core::marker::Sized) -> usize {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_530(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_2<core_cmp_Ordering_31> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_541(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn iterators_slice_chunks_exact_iter_6(key: [u128; 128usize], data: Vec<u8>) -> Result<()> {
    let iter_0: core_slice_iter_ChunksExact_6<u8> = (impl_core_slice_chunks_exact_17::<u8>(data, 16usize))?;
    (iterators_slice_chunks_exact_iter_6_loop0(iter_0, key))
}

pub fn iterators_key_iter_slice_iter_7(key: iterators_Key_0, data: Vec<u8>) -> Result<()> {
    let iter_0: core_slice_iter_Iter_5<u8> = (impl_core_slice_iter_15::<u8>(data))?;
    (iterators_key_iter_slice_iter_7_loop0(iter_0, key))
}

pub fn iterators_slice_iter_mut_while_early_return_4(s: [u16; 256usize], b: bool) -> Result<[u16; 256usize]> {
    let (v0, to_slice_mut_back_1): (Vec<u16>, Box<dyn FnOnce(Vec<u16>) -> [u16; 256usize]>) = Ok(unimplemented!("FBuiltin call"))?;
    let (it_2, iter_mut_back_3): (core_slice_iter_IterMut_4<u16>, Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> Vec<u16>>) = (impl_core_slice_iter_mut_13::<u16>(v0))?;
    let back_4: core_slice_iter_IterMut_4<u16> = (iterators_slice_iter_mut_while_early_return_4_loop0(it_2, (Box::new(move |v5: core_slice_iter_IterMut_4<u16>| -> core_slice_iter_IterMut_4<u16> { v5 }) as Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>), b))?;
    let v6: Vec<u16> = (iter_mut_back_3(back_4));
    Ok((to_slice_mut_back_1(v6)))
}

pub fn iterators_slice_iter_mut_while_early_return_two_bools_5(s: [u16; 256usize], b0: bool, b1: bool) -> Result<[u16; 256usize]> {
    let (v0, to_slice_mut_back_1): (Vec<u16>, Box<dyn FnOnce(Vec<u16>) -> [u16; 256usize]>) = Ok(unimplemented!("FBuiltin call"))?;
    let (it_2, iter_mut_back_3): (core_slice_iter_IterMut_4<u16>, Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> Vec<u16>>) = (impl_core_slice_iter_mut_13::<u16>(v0))?;
    let back_4: core_slice_iter_IterMut_4<u16> = (iterators_slice_iter_mut_while_early_return_two_bools_5_loop0(it_2, (Box::new(move |v5: core_slice_iter_IterMut_4<u16>| -> core_slice_iter_IterMut_4<u16> { v5 }) as Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>), b0, b1))?;
    let v6: Vec<u16> = (iter_mut_back_3(back_4));
    Ok((to_slice_mut_back_1(v6)))
}

pub fn iterators_copy_arrays_8(src: [u8; 256usize], dst: [u8; 256usize]) -> Result<[u8; 256usize]> {
    (iterators_copy_arrays_8_loop0(core_ops_range_Range_1 { start: 0usize, end: 256usize }, src, dst))
}

pub fn iterators_slice_iter_mut_while_2(b: bool, s: Vec<u16>) -> Result<Vec<u16>> {
    let (it_0, iter_mut_back_1): (core_slice_iter_IterMut_4<u16>, Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> Vec<u16>>) = (impl_core_slice_iter_mut_13::<u16>(s))?;
    let back_2: core_slice_iter_IterMut_4<u16> = (iterators_slice_iter_mut_while_2_loop0(it_0, (Box::new(move |v3: core_slice_iter_IterMut_4<u16>| -> core_slice_iter_IterMut_4<u16> { v3 }) as Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>), b))?;
    Ok((iter_mut_back_1(back_2)))
}

pub fn iterators_slice_iter_while_3(b: bool, s: Vec<u16>) -> Result<()> {
    let it_0: core_slice_iter_Iter_5<u16> = (impl_core_slice_iter_15::<u16>(s))?;
    (iterators_slice_iter_while_3_loop0(it_0, b))
}

pub fn iterators_iter_range_step_by_1(n: usize) -> Result<()> {
    let iter_0: core_iter_adapters_step_by_StepBy_3<core_ops_range_Range_1<usize>> = (impl_core_iter_range_step_by_101::<usize>(core_ops_range_Range_1 { start: 0usize, end: n }, 2usize))?;
    (iterators_iter_range_step_by_1_loop0(iter_0))
}

pub fn iterators_iter_range_0() -> Result<()> {
    (iterators_iter_range_0_loop0(core_ops_range_Range_1 { start: 0usize, end: 32usize }))
}

pub fn iterators_slice_chunks_exact_iter_6_loop0(iter: core_slice_iter_ChunksExact_6<u8>, key: [u128; 128usize]) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_chunks_exact_iter_6_loop1(iter: core_slice_iter_Iter_5<u128>) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_key_iter_slice_iter_7_loop0(iter: core_slice_iter_Iter_5<u8>, key: iterators_Key_0) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_key_iter_slice_iter_7_loop1(iter: core_slice_iter_Iter_5<u128>) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_early_return_4_loop0(it: core_slice_iter_IterMut_4<u16>, back: Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>, b: bool) -> Result<core_slice_iter_IterMut_4<u16>> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_early_return_4_loop1(b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_early_return_two_bools_5_loop0(it: core_slice_iter_IterMut_4<u16>, back: Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>, b0: bool, b1: bool) -> Result<core_slice_iter_IterMut_4<u16>> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_early_return_two_bools_5_loop1(b0: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_copy_arrays_8_loop0(iter: core_ops_range_Range_1<usize>, src: [u8; 256usize], dst: [u8; 256usize]) -> Result<[u8; 256usize]> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_2_loop0(it: core_slice_iter_IterMut_4<u16>, back: Box<dyn FnOnce(core_slice_iter_IterMut_4<u16>) -> core_slice_iter_IterMut_4<u16>>, b: bool) -> Result<core_slice_iter_IterMut_4<u16>> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_mut_while_2_loop1(b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_while_3_loop0(it: core_slice_iter_Iter_5<u16>, b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_slice_iter_while_3_loop1(b: bool) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_iter_range_step_by_1_loop0(iter: core_iter_adapters_step_by_StepBy_3<core_ops_range_Range_1<usize>>) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn iterators_iter_range_0_loop0(iter: core_ops_range_Range_1<usize>) -> Result<()> {
    panic!("LoopOp placeholder")
}

