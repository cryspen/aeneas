
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

pub struct loops_nested_rec_Key_0 {
    pub seed: [u8; 32usize],
    pub atranspose: [u16; 32usize],
}

// TODO: opaque type alloc_vec_Vec_2 — emitting marker struct.
pub struct alloc_vec_Vec_2<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_3;

// TODO: opaque type core_iter_adapters_step_by_StepBy_4 — emitting marker struct.
pub struct core_iter_adapters_step_by_StepBy_4<I>(pub core::marker::PhantomData<fn() -> (I,)>);

pub struct core_ops_range_Range_5<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub enum core_option_Option_6<T> {
    None,
    Some(T),
}

pub enum core_cmp_Ordering_31 {
    Less,
    Equal,
    Greater,
}

pub fn impl_core_convert_into_14<T, U>(p0: impl core::marker::Sized) -> Result<U> where T: 'static, U: 'static {
    unimplemented!("opaque body")
}

pub fn alloc_vec_from_elem_16<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<alloc_vec_Vec_2<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_step_by_18<Self_, Clause0_Item>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_4<Self_>> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_adapters_step_by_next_20<I, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_6<Clause0_Item>, core_iter_adapters_step_by_StepBy_4<I>)> where I: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_next_21<A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_6<A>, core_ops_range_Range_5<A>)> where A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_index_mut_22<T, I, A, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> alloc_vec_Vec_2<T>>)> where T: 'static, I: 'static, A: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_convert_From_from_23<Self_, T>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static, T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_convert_num_from_24(p0: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_25<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_27(p0: impl core::marker::Sized) -> u8 {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_30<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_6<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_step_by_112<A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_4<core_ops_range_Range_5<A>>> where A: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_steps_between_182<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_6<usize>)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_forward_checked_183<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_range_Step_backward_checked_186<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<Self_>> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_steps_between_189(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(usize, core_option_Option_6<usize>)> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_forward_checked_190(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<usize>> {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_range_backward_checked_193(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<usize>> {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_272<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_273<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_6<Clause0_Output>, Box<dyn FnOnce(core_option_Option_6<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_274<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_275<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_276<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_277<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_278<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_279<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_6<T>, Box<dyn FnOnce(core_option_Option_6<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_280<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_281<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_282<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_283<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(T, Box<dyn FnOnce(T) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_310<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<core_cmp_Ordering_31>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_319<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_322(p0: impl core::marker::Sized) -> usize {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_partial_cmp_324(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> core_option_Option_6<core_cmp_Ordering_31> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_338(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn loops_nested_rec_ntt_layer_5(a: [u16; 256usize], k: usize, len: usize) -> Result<[u16; 256usize]> {
    (loops_nested_rec_ntt_layer_5_loop0(a, k, len, 0usize))
}

pub fn loops_nested_rec_generate_matrix_11(key: loops_nested_rec_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize]) -> Result<(loops_nested_rec_Key_0, [u8; 8usize], [u8; 8usize])> {
    let coordinates_0: [u8; 2usize] = unimplemented!("placeholder");
    let state_base_1: [u8; 8usize] = (loops_nested_rec_shake_init_6(state_base))?;
    let v2: Vec<u8> = Ok(unimplemented!("FBuiltin call"))?;
    let state_base_3: [u8; 8usize] = (loops_nested_rec_shake_append_7(state_base_1, v2))?;
    let (key_4, state_work_5): (loops_nested_rec_Key_0, [u8; 8usize]) = (loops_nested_rec_generate_matrix_11_loop0(key, state_base_3, state_work, coordinates_0, 0u8))?;
    Ok((key_4, state_base_3, state_work_5))
}

pub fn loops_nested_rec_mul_add_as_plus_e_12<const N: usize>(out: Vec<u16>, s: Vec<u16>, seed_a: [u8; 16usize]) -> Result<Vec<u16>> {
    let v0: usize = (4usize.checked_mul(0usize).ok_or(()))?;
    let v1: usize = (v0.checked_mul(2usize).ok_or(()))?;
    let a_row_temp_2: alloc_vec_Vec_2<u8> = (alloc_vec_from_elem_16::<u8>(0u8, v1))?;
    let v3: usize = (v0.checked_mul(2usize).ok_or(()))?;
    let _: alloc_vec_Vec_2<u8> = (alloc_vec_from_elem_16::<u8>(0u8, v3))?;
    let iter_4: core_iter_adapters_step_by_StepBy_4<core_ops_range_Range_5<usize>> = (impl_core_iter_range_step_by_112::<usize>(core_ops_range_Range_5 { start: 0usize, end: 0usize }, 8usize))?;
    let _: () = (loops_nested_rec_mul_add_as_plus_e_12_loop0(iter_4, a_row_temp_2))?;
    Ok(out)
}

pub fn loops_nested_rec_update_array_2() -> Result<()> {
    let out_0: [u8; 4usize] = unimplemented!("placeholder");
    (loops_nested_rec_update_array_2_loop0(out_0, 0usize))
}

pub fn loops_nested_rec_sum_1(m: u32, n: u32) -> Result<u32> {
    (loops_nested_rec_sum_1_loop0(m, n, 0u32, 0u32))
}

pub fn loops_nested_rec_iter_0(m: u32, n: u32) -> Result<()> {
    (loops_nested_rec_iter_0_loop0(m, n, 0u32))
}

pub fn loops_nested_rec_generate_matrix_inner_10(key: loops_nested_rec_Key_0, state: [u8; 8usize]) -> Result<(loops_nested_rec_Key_0, [u8; 8usize])> {
    (loops_nested_rec_generate_matrix_inner_10_loop0(key, state, 0usize))
}

pub fn loops_nested_rec_mod_sub_4(a: u32, b: u32) -> Result<u32> {
    let v0: u32 = (a.checked_add(3329u32).ok_or(()))?;
    let v1: u32 = (b.checked_rem(3329u32).ok_or(()))?;
    let v2: u32 = (v0.checked_sub(v1).ok_or(()))?;
    (v2.checked_rem(3329u32).ok_or(()))
}

pub fn loops_nested_rec_mod_add_3(a: u32, b: u32) -> Result<u32> {
    let v0: u32 = (a.checked_add(b).ok_or(()))?;
    (v0.checked_rem(3329u32).ok_or(()))
}

pub fn impl_loops_nested_rec_atranspose_mut_15(self_: loops_nested_rec_Key_0) -> Result<([u16; 32usize], Box<dyn FnOnce([u16; 32usize]) -> loops_nested_rec_Key_0>)> {
    let back_0: Box<dyn FnOnce([u16; 32usize]) -> loops_nested_rec_Key_0> = (Box::new(move |v1: [u16; 32usize]| -> loops_nested_rec_Key_0 { loops_nested_rec_Key_0 { seed: self_.seed, atranspose: v1 } }) as Box<dyn FnOnce([u16; 32usize]) -> loops_nested_rec_Key_0>);
    Ok((self_.atranspose, back_0))
}

pub fn loops_nested_rec_shake_init_6(_state: [u8; 8usize]) -> Result<[u8; 8usize]> {
    Ok(_state)
}

pub fn loops_nested_rec_shake_append_7(_state: [u8; 8usize], _data: Vec<u8>) -> Result<[u8; 8usize]> {
    Ok(_state)
}

pub fn loops_nested_rec_shake_state_copy_8(_src: [u8; 8usize], _dst: [u8; 8usize]) -> Result<[u8; 8usize]> {
    Ok(_dst)
}

pub fn loops_nested_rec_sample_ntt_9(_state: [u8; 8usize], _dst: u16) -> Result<([u8; 8usize], u16)> {
    Ok((_state, _dst))
}

pub fn loops_nested_rec_FACTORS_13() -> [u16; 32usize] {
    [2285u16, 2571u16, 2970u16, 1812u16, 1493u16, 1422u16, 287u16, 202u16, 3158u16, 622u16, 1577u16, 182u16, 962u16, 2127u16, 1855u16, 1468u16, 573u16, 2004u16, 264u16, 383u16, 2500u16, 1458u16, 1727u16, 3199u16, 2648u16, 1017u16, 732u16, 608u16, 1787u16, 411u16, 3124u16, 1758u16]
}

pub fn loops_nested_rec_ntt_layer_5_loop0(a: [u16; 256usize], k: usize, len: usize, start: usize) -> Result<[u16; 256usize]> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_ntt_layer_5_loop1(a: [u16; 256usize], len: usize, start: usize, factor: u32, j: usize) -> Result<[u16; 256usize]> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_generate_matrix_11_loop0(key: loops_nested_rec_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize], coordinates: [u8; 2usize], i: u8) -> Result<(loops_nested_rec_Key_0, [u8; 8usize])> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_generate_matrix_11_loop1(key: loops_nested_rec_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize], coordinates: [u8; 2usize], i: u8, j: u8) -> Result<(loops_nested_rec_Key_0, [u8; 8usize], [u8; 2usize])> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_mul_add_as_plus_e_12_loop0(iter: core_iter_adapters_step_by_StepBy_4<core_ops_range_Range_5<usize>>, a_row_temp: alloc_vec_Vec_2<u8>) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_mul_add_as_plus_e_12_loop1(iter: core_ops_range_Range_5<usize>, a_row_temp: alloc_vec_Vec_2<u8>, j: usize) -> Result<alloc_vec_Vec_2<u8>> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_update_array_2_loop0(out: [u8; 4usize], i: usize) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_update_array_2_loop1(out: [u8; 4usize], j: usize) -> Result<[u8; 4usize]> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_sum_1_loop0(m: u32, n: u32, s: u32, i: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_sum_1_loop1(n: u32, s: u32, j: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_iter_0_loop0(m: u32, n: u32, i: u32) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_iter_0_loop1(n: u32, j: u32) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_nested_rec_generate_matrix_inner_10_loop0(key: loops_nested_rec_Key_0, state: [u8; 8usize], j: usize) -> Result<(loops_nested_rec_Key_0, [u8; 8usize])> {
    panic!("LoopOp placeholder")
}

