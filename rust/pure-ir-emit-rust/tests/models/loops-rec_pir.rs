
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

pub enum loops_rec_List_0<T> {
    Cons(T, Box<loops_rec_List_0<T>>),
    Nil,
}

pub enum loops_rec_AList_1<T> {
    Cons(usize, T, Box<loops_rec_AList_1<T>>),
    Nil,
}

// TODO: opaque type alloc_vec_Vec_2 — emitting marker struct.
pub struct alloc_vec_Vec_2<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_3;

pub struct loops_rec_issue500_2_A_4([bool; 1usize]);

pub struct loops_rec_issue500_3_A_5([bool; 1usize]);

pub enum core_option_Option_6<T> {
    None,
    Some(T),
}

pub fn impl_alloc_vec_len_40<T, A>(p0: impl core::marker::Sized) -> usize where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_index_mut_41<T, I, A, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> alloc_vec_Vec_2<T>>)> where T: 'static, I: 'static, A: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_index_42<T, I, A, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where T: 'static, I: 'static, A: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_len_46<T>(p0: impl core::marker::Sized) -> usize where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_49<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<Clause0_Output>> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_mut_50<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_6<Clause0_Output>, Box<dyn FnOnce(core_option_Option_6<Clause0_Output>) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_51<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_get_unchecked_mut_52<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_53<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn core_slice_index_SliceIndex_index_mut_54<Self_, T, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(Clause0_Output, Box<dyn FnOnce(Clause0_Output) -> T>)> where Self_: 'static, T: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_55<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_6<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_mut_56<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_option_Option_6<T>, Box<dyn FnOnce(core_option_Option_6<T>) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_57<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_get_unchecked_mut_58<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_59<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_index_index_mut_60<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(T, Box<dyn FnOnce(T) -> Vec<T>>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn loops_rec_issue400_2_32(a: i32, b: i32, c: i32, conds: Vec<bool>) -> Result<(i32, i32, i32)> {
    let (y_0, z_1, back_2): (i32, i32, Box<dyn FnOnce(i32) -> Box<dyn FnOnce(i32) -> (i32, i32, i32)>>) = (loops_rec_issue400_2_32_loop0((Box::new(move |v3: i32| -> Box<dyn FnOnce(i32) -> (i32, i32, i32)> { (Box::new(move |v4: i32| -> (i32, i32, i32) { (v3, v4, c) }) as Box<dyn FnOnce(i32) -> (i32, i32, i32)>) }) as Box<dyn FnOnce(i32) -> Box<dyn FnOnce(i32) -> (i32, i32, i32)>>), conds, a, b, 0usize))?;
    let y_5: i32 = (y_0.checked_add(3i32).ok_or(()))?;
    let z_6: i32 = (z_1.checked_add(5i32).ok_or(()))?;
    Ok(((back_2(y_5))(z_6)))
}

pub fn loops_rec_list_nth_mut_pair_15<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (v0, v1, back_2, back_3): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_pair_15_loop0::<T>(ls0, ls1, i))?;
    Ok(((v0, v1), back_2, back_3))
}

pub fn loops_rec_list_nth_shared_pair_16<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T)> where T: 'static {
    (loops_rec_list_nth_shared_pair_16_loop0::<T>(ls0, ls1, i))
}

pub fn loops_rec_list_nth_mut_pair_merge_17<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce((T, T)) -> (loops_rec_List_0<T>, loops_rec_List_0<T>)>)> where T: 'static {
    let (v0, v1, back_2, back_3): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_pair_merge_17_loop0::<T>(ls0, ls1, i))?;
    let back_4: Box<dyn FnOnce((T, T)) -> (loops_rec_List_0<T>, loops_rec_List_0<T>)> = (Box::new(move |v5: (T, T)| -> (loops_rec_List_0<T>, loops_rec_List_0<T>) { {
    let (v6, v7): (T, T) = v5;
    let ls0_8: loops_rec_List_0<T> = (back_2(v6));
    let ls1_9: loops_rec_List_0<T> = (back_3(v7));
    (ls0_8, ls1_9)
} }) as Box<dyn FnOnce((T, T)) -> (loops_rec_List_0<T>, loops_rec_List_0<T>)>);
    Ok(((v0, v1), back_4))
}

pub fn loops_rec_list_nth_shared_pair_merge_18<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T)> where T: 'static {
    (loops_rec_list_nth_shared_pair_merge_18_loop0::<T>(ls0, ls1, i))
}

pub fn loops_rec_list_nth_mut_shared_pair_19<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (v0, v1, back_2): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_shared_pair_19_loop0::<T>(ls0, ls1, i))?;
    Ok(((v0, v1), back_2))
}

pub fn loops_rec_list_nth_mut_shared_pair_merge_20<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (v0, v1, back_2): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_shared_pair_merge_20_loop0::<T>(ls0, ls1, i))?;
    Ok(((v0, v1), back_2))
}

pub fn loops_rec_list_nth_shared_mut_pair_21<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (v0, v1, back_2): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_shared_mut_pair_21_loop0::<T>(ls0, ls1, i))?;
    Ok(((v0, v1), back_2))
}

pub fn loops_rec_list_nth_shared_mut_pair_merge_22<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<((T, T), Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (v0, v1, back_2): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_shared_mut_pair_merge_22_loop0::<T>(ls0, ls1, i))?;
    Ok(((v0, v1), back_2))
}

pub fn loops_rec_insert_in_list_36<T>(key: usize, value: T, ls: loops_rec_AList_1<T>) -> Result<(bool, loops_rec_AList_1<T>)> where T: 'static {
    (loops_rec_insert_in_list_36_loop0::<T>(key, value, ls))
}

pub fn loops_rec_decode_38(pe_dst: Vec<u8>) -> Result<(bool, Vec<u8>)> {
    (loops_rec_decode_38_loop0(pe_dst, 0usize))
}

pub fn loops_rec_as_radix_minimized_39() -> Result<()> {
    let scalar_0: [u64; 4usize] = unimplemented!("placeholder");
    (loops_rec_as_radix_minimized_39_loop0(scalar_0, 0usize))
}

pub fn loops_rec_issue270_30(v: loops_rec_List_0<loops_rec_List_0<u8>>) -> Result<core_option_Option_6<loops_rec_List_0<u8>>> {
    match v {
    loops_rec_List_0::Cons(h_0, __rec_1) => {
    let t_2: loops_rec_List_0<loops_rec_List_0<u8>> = (loops_rec_issue270_box_get_borrow_45::<loops_rec_List_0<loops_rec_List_0<u8>>>((*__rec_1)))?;
    let last_3: loops_rec_List_0<u8> = (loops_rec_issue270_30_loop0(t_2, h_0))?;
    Ok(core_option_Option_6::Some(last_3))
},
    loops_rec_List_0::Nil => Ok(core_option_Option_6::<loops_rec_List_0<u8>>::None),
}
}

pub fn loops_rec_get_elem_mut_9(slots: alloc_vec_Vec_2<loops_rec_List_0<usize>>, x: usize) -> Result<(usize, Box<dyn FnOnce(usize) -> alloc_vec_Vec_2<loops_rec_List_0<usize>>>)> {
    let (ls_0, index_mut_back_1): (loops_rec_List_0<usize>, Box<dyn FnOnce(loops_rec_List_0<usize>) -> alloc_vec_Vec_2<loops_rec_List_0<usize>>>) = (impl_alloc_vec_index_mut_41::<loops_rec_List_0<usize>, usize, alloc_alloc_Global_3, loops_rec_List_0<usize>>(slots, 0usize))?;
    let (v2, back_3): (usize, Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>>) = (loops_rec_get_elem_mut_9_loop0(x, ls_0))?;
    let back_4: Box<dyn FnOnce(usize) -> alloc_vec_Vec_2<loops_rec_List_0<usize>>> = (Box::new(move |v5: usize| -> alloc_vec_Vec_2<loops_rec_List_0<usize>> { {
    let v6: loops_rec_List_0<usize> = (back_3(v5));
    (index_mut_back_1(v6))
} }) as Box<dyn FnOnce(usize) -> alloc_vec_Vec_2<loops_rec_List_0<usize>>>);
    Ok((v2, back_4))
}

pub fn loops_rec_get_elem_shared_10(slots: alloc_vec_Vec_2<loops_rec_List_0<usize>>, x: usize) -> Result<usize> {
    let ls_0: loops_rec_List_0<usize> = (impl_alloc_vec_index_42::<loops_rec_List_0<usize>, usize, alloc_alloc_Global_3, loops_rec_List_0<usize>>(slots, 0usize))?;
    (loops_rec_get_elem_shared_10_loop0(x, ls_0))
}

pub fn loops_rec_issue400_1_31(a: i32, b: i32, cond: bool) -> Result<(i32, i32)> {
    (loops_rec_issue400_1_31_loop0((Box::new(move |v0: i32| -> (i32, i32) { (v0, b) }) as Box<dyn FnOnce(i32) -> (i32, i32)>), cond, a, 0i32))
}

pub fn loops_rec_sum_with_mut_borrows_2(max: u32) -> Result<u32> {
    let s_0: u32 = (loops_rec_sum_with_mut_borrows_2_loop0(max, 0u32, 0u32))?;
    (s_0.checked_mul(2u32).ok_or(()))
}

pub fn loops_rec_list_nth_mut_with_id_13<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<(T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    let (ls_0, id_mut_back_1): (loops_rec_List_0<T>, Box<dyn FnOnce(loops_rec_List_0<T>) -> loops_rec_List_0<T>>) = (loops_rec_id_mut_11::<T>(ls))?;
    let (v2, back_3): (T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_with_id_13_loop0::<T>(i, ls_0))?;
    let back_4: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v5: T| -> loops_rec_List_0<T> { {
    let v6: loops_rec_List_0<T> = (back_3(v5));
    (id_mut_back_1(v6))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v2, back_4))
}

pub fn loops_rec_list_nth_shared_with_id_14<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<T> where T: 'static {
    let ls_0: loops_rec_List_0<T> = (loops_rec_id_shared_12::<T>(ls))?;
    (loops_rec_list_nth_shared_with_id_14_loop0::<T>(i, ls_0))
}

pub fn loops_rec_copy_carray_33(a: [u32; 2usize]) -> Result<[u32; 2usize]> {
    (loops_rec_copy_carray_33_loop0(a, 0usize))
}

pub fn loops_rec_sum_with_shared_borrows_3(max: u32) -> Result<u32> {
    let s_0: u32 = (loops_rec_sum_with_shared_borrows_3_loop0(max, 0u32, 0u32))?;
    (s_0.checked_mul(2u32).ok_or(()))
}

pub fn loops_rec_clear_5(v: alloc_vec_Vec_2<u32>) -> Result<alloc_vec_Vec_2<u32>> {
    (loops_rec_clear_5_loop0(v, 0usize))
}

pub fn loops_rec_list_mem_6(x: u32, ls: loops_rec_List_0<u32>) -> Result<bool> {
    (loops_rec_list_mem_6_loop0(x, ls))
}

pub fn loops_rec_sum_1(max: u32) -> Result<u32> {
    let s_0: u32 = (loops_rec_sum_1_loop0(max, 0u32, 0u32))?;
    (s_0.checked_mul(2u32).ok_or(()))
}

pub fn loops_rec_list_nth_mut_7<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<(T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    (loops_rec_list_nth_mut_7_loop0::<T>(ls, i))
}

pub fn loops_rec_list_nth_shared_8<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<T> where T: 'static {
    (loops_rec_list_nth_shared_8_loop0::<T>(ls, i))
}

pub fn loops_rec_sum_array_4<const N: usize>(a: [u32; N]) -> Result<u32> {
    (loops_rec_sum_array_4_loop0::<N>(a, 0usize, 0u32))
}

pub fn loops_rec_iter_local_mut_borrow_34() -> Result<()> {
    (loops_rec_iter_local_mut_borrow_34_loop0(0i32))
}

pub fn loops_rec_reborrow_const_37() -> Result<()> {
    (loops_rec_reborrow_const_37_loop0())
}

pub fn loops_rec_issue500_2_27(s: [bool; 1usize]) -> Result<[bool; 1usize]> {
    let _: () = (loops_rec_issue500_2_27_loop0())?;
    Ok(s)
}

pub fn loops_rec_iter_local_shared_borrow_35() -> Result<()> {
    (loops_rec_iter_local_shared_borrow_35_loop0())
}

pub fn loops_rec_issue500_1_26(s: bool) -> Result<bool> {
    (loops_rec_issue500_1_26_loop0(s))
}

pub fn loops_rec_issue351_29(h: u8, t: loops_rec_List_0<u8>) -> Result<u8> {
    (loops_rec_issue351_29_loop0(t, h))
}

pub fn loops_rec_iter_0(max: u32) -> Result<u32> {
    (loops_rec_iter_0_loop0(max, 0u32))
}

pub fn loops_rec_incr_ignore_input_mut_borrow_24(a: u32, i: u32) -> Result<u32> {
    let a_0: u32 = (a.checked_add(1u32).ok_or(()))?;
    let _: () = (loops_rec_incr_ignore_input_mut_borrow_24_loop0(i))?;
    Ok(a_0)
}

pub fn loops_rec_issue500_3_28(s: [bool; 1usize]) -> Result<[bool; 1usize]> {
    let _: () = (loops_rec_issue500_3_28_loop0())?;
    Ok(s)
}

pub fn loops_rec_ignore_input_mut_borrow_23(_a: u32, i: u32) -> Result<u32> {
    let _: () = (loops_rec_ignore_input_mut_borrow_23_loop0(i))?;
    Ok(_a)
}

pub fn loops_rec_ignore_input_shared_borrow_25(_a: u32, i: u32) -> Result<u32> {
    let _: () = (loops_rec_ignore_input_shared_borrow_25_loop0(i))?;
    Ok(_a)
}

pub fn loops_rec_id_mut_11<T>(ls: loops_rec_List_0<T>) -> Result<(loops_rec_List_0<T>, Box<dyn FnOnce(loops_rec_List_0<T>) -> loops_rec_List_0<T>>)> where T: 'static {
    Ok((ls, (Box::new(move |ls_0: loops_rec_List_0<T>| -> loops_rec_List_0<T> { ls_0 }) as Box<dyn FnOnce(loops_rec_List_0<T>) -> loops_rec_List_0<T>>)))
}

pub fn loops_rec_issue270_box_get_borrow_45<T>(x: T) -> Result<T> where T: 'static {
    Ok(x)
}

pub fn loops_rec_issue500_1_bar_43(_a: bool) -> Result<bool> {
    Ok(_a)
}

pub fn loops_rec_issue500_2_bar_44(_a: [bool; 1usize]) -> Result<[bool; 1usize]> {
    Ok(_a)
}

pub fn loops_rec_id_shared_12<T>(ls: loops_rec_List_0<T>) -> Result<loops_rec_List_0<T>> where T: 'static {
    Ok(ls)
}

pub fn loops_rec_reborrow_const_reborrow_48(x: u64) -> Result<u64> {
    Ok(x)
}

pub fn loops_rec_copy_carray_CARRAY_61() -> [u32; 2usize] {
    [0u32, 1u32]
}

pub fn loops_rec_issue400_2_32_loop0(back: Box<dyn FnOnce(i32) -> Box<dyn FnOnce(i32) -> (i32, i32, i32)>>, conds: Vec<bool>, y: i32, z: i32, i: usize) -> Result<(i32, i32, Box<dyn FnOnce(i32) -> Box<dyn FnOnce(i32) -> (i32, i32, i32)>>)> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_list_nth_mut_pair_15_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>), (Box::new(move |v5: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v5, Box::new((*__rec_3))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_6: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v7, v8, back_9, back_10): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_pair_15_loop0::<T>((*__rec_1), (*__rec_3), i_6))?;
    let back_11: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v12: T| -> loops_rec_List_0<T> { {
    let v13: loops_rec_List_0<T> = (back_9(v12));
    loops_rec_List_0::Cons(x0_0, Box::new(v13))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    let back_14: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v15: T| -> loops_rec_List_0<T> { {
    let v16: loops_rec_List_0<T> = (back_10(v15));
    loops_rec_List_0::Cons(x1_2, Box::new(v16))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v7, v8, back_11, back_14))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_pair_16_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2)) } else { {
    let i_4: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (loops_rec_list_nth_shared_pair_16_loop0::<T>((*__rec_1), (*__rec_3), i_4))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_mut_pair_merge_17_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>), (Box::new(move |v5: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v5, Box::new((*__rec_3))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_6: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v7, v8, back_9, back_10): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_pair_merge_17_loop0::<T>((*__rec_1), (*__rec_3), i_6))?;
    let back_11: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v12: T| -> loops_rec_List_0<T> { {
    let v13: loops_rec_List_0<T> = (back_9(v12));
    loops_rec_List_0::Cons(x0_0, Box::new(v13))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    let back_14: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v15: T| -> loops_rec_List_0<T> { {
    let v16: loops_rec_List_0<T> = (back_10(v15));
    loops_rec_List_0::Cons(x1_2, Box::new(v16))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v7, v8, back_11, back_14))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_pair_merge_18_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2)) } else { {
    let i_4: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (loops_rec_list_nth_shared_pair_merge_18_loop0::<T>((*__rec_1), (*__rec_3), i_4))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_mut_shared_pair_19_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_5: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v6, v7, back_8): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_shared_pair_19_loop0::<T>((*__rec_1), (*__rec_3), i_5))?;
    let back_9: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v10: T| -> loops_rec_List_0<T> { {
    let v11: loops_rec_List_0<T> = (back_8(v10));
    loops_rec_List_0::Cons(x0_0, Box::new(v11))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v6, v7, back_9))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_mut_shared_pair_merge_20_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_5: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v6, v7, back_8): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_shared_pair_merge_20_loop0::<T>((*__rec_1), (*__rec_3), i_5))?;
    let back_9: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v10: T| -> loops_rec_List_0<T> { {
    let v11: loops_rec_List_0<T> = (back_8(v10));
    loops_rec_List_0::Cons(x0_0, Box::new(v11))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v6, v7, back_9))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_mut_pair_21_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_3))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_5: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v6, v7, back_8): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_shared_mut_pair_21_loop0::<T>((*__rec_1), (*__rec_3), i_5))?;
    let back_9: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v10: T| -> loops_rec_List_0<T> { {
    let v11: loops_rec_List_0<T> = (back_8(v10));
    loops_rec_List_0::Cons(x1_2, Box::new(v11))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v6, v7, back_9))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_mut_pair_merge_22_loop0<T>(ls0: loops_rec_List_0<T>, ls1: loops_rec_List_0<T>, i: u32) -> Result<(T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls0 {
    loops_rec_List_0::Cons(x0_0, __rec_1) => match ls1 {
    loops_rec_List_0::Cons(x1_2, __rec_3) => (if (i == 0u32) { Ok((x0_0, x1_2, (Box::new(move |v4: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v4, Box::new((*__rec_3))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_5: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v6, v7, back_8): (T, T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_shared_mut_pair_merge_22_loop0::<T>((*__rec_1), (*__rec_3), i_5))?;
    let back_9: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v10: T| -> loops_rec_List_0<T> { {
    let v11: loops_rec_List_0<T> = (back_8(v10));
    loops_rec_List_0::Cons(x1_2, Box::new(v11))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v6, v7, back_9))
} }),
    loops_rec_List_0::Nil => Err(()),
},
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_insert_in_list_36_loop0<T>(key: usize, value: T, ls: loops_rec_AList_1<T>) -> Result<(bool, loops_rec_AList_1<T>)> where T: 'static {
    match ls {
    loops_rec_AList_1::Cons(ckey_0, cvalue_1, __rec_2) => (if (ckey_0 == key) { Ok((false, loops_rec_AList_1::Cons(ckey_0, value, Box::new((*__rec_2))))) } else { {
    let (v3, back_4): (bool, loops_rec_AList_1<T>) = (loops_rec_insert_in_list_36_loop0::<T>(key, value, (*__rec_2)))?;
    let back_5: loops_rec_AList_1<T> = loops_rec_AList_1::Cons(ckey_0, cvalue_1, Box::new(back_4));
    Ok((v3, back_5))
} }),
    loops_rec_AList_1::Nil => Ok((true, loops_rec_AList_1::Cons(key, value, Box::new(loops_rec_AList_1::<T>::Nil)))),
}
}

pub fn loops_rec_decode_38_loop0(pe_dst: Vec<u8>, i: usize) -> Result<(bool, Vec<u8>)> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_decode_38_loop1(dst_coeff: u8) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_as_radix_minimized_39_loop0(scalar: [u64; 4usize], i: usize) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_issue270_30_loop0(t: loops_rec_List_0<loops_rec_List_0<u8>>, last: loops_rec_List_0<u8>) -> Result<loops_rec_List_0<u8>> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_get_elem_mut_9_loop0(x: usize, ls: loops_rec_List_0<usize>) -> Result<(usize, Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>>)> {
    match ls {
    loops_rec_List_0::Cons(y_0, __rec_1) => (if (y_0 == x) { Ok((y_0, (Box::new(move |v2: usize| -> loops_rec_List_0<usize> { loops_rec_List_0::Cons(v2, Box::new((*__rec_1))) }) as Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>>))) } else { {
    let (v3, back_4): (usize, Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>>) = (loops_rec_get_elem_mut_9_loop0(x, (*__rec_1)))?;
    let back_5: Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>> = (Box::new(move |v6: usize| -> loops_rec_List_0<usize> { {
    let v7: loops_rec_List_0<usize> = (back_4(v6));
    loops_rec_List_0::Cons(y_0, Box::new(v7))
} }) as Box<dyn FnOnce(usize) -> loops_rec_List_0<usize>>);
    Ok((v3, back_5))
} }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_get_elem_shared_10_loop0(x: usize, ls: loops_rec_List_0<usize>) -> Result<usize> {
    match ls {
    loops_rec_List_0::Cons(y_0, __rec_1) => (if (y_0 == x) { Ok(y_0) } else { (loops_rec_get_elem_shared_10_loop0(x, (*__rec_1))) }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_issue400_1_31_loop0(back: Box<dyn FnOnce(i32) -> (i32, i32)>, cond: bool, y: i32, i: i32) -> Result<(i32, i32)> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_sum_with_mut_borrows_2_loop0(max: u32, i: u32, s: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_list_nth_mut_with_id_13_loop0<T>(i: u32, ls: loops_rec_List_0<T>) -> Result<(T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls {
    loops_rec_List_0::Cons(x_0, __rec_1) => (if (i == 0u32) { Ok((x_0, (Box::new(move |v2: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v2, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_3: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v4, back_5): (T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_with_id_13_loop0::<T>(i_3, (*__rec_1)))?;
    let back_6: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v7: T| -> loops_rec_List_0<T> { {
    let v8: loops_rec_List_0<T> = (back_5(v7));
    loops_rec_List_0::Cons(x_0, Box::new(v8))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v4, back_6))
} }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_with_id_14_loop0<T>(i: u32, ls: loops_rec_List_0<T>) -> Result<T> where T: 'static {
    match ls {
    loops_rec_List_0::Cons(x_0, __rec_1) => (if (i == 0u32) { Ok(x_0) } else { {
    let i_2: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (loops_rec_list_nth_shared_with_id_14_loop0::<T>(i_2, (*__rec_1)))
} }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_copy_carray_33_loop0(a: [u32; 2usize], i: usize) -> Result<[u32; 2usize]> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_sum_with_shared_borrows_3_loop0(max: u32, i: u32, s: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_clear_5_loop0(v: alloc_vec_Vec_2<u32>, i: usize) -> Result<alloc_vec_Vec_2<u32>> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_list_mem_6_loop0(x: u32, ls: loops_rec_List_0<u32>) -> Result<bool> {
    match ls {
    loops_rec_List_0::Cons(y_0, __rec_1) => (if (y_0 == x) { Ok(true) } else { (loops_rec_list_mem_6_loop0(x, (*__rec_1))) }),
    loops_rec_List_0::Nil => Ok(false),
}
}

pub fn loops_rec_sum_1_loop0(max: u32, i: u32, s: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_list_nth_mut_7_loop0<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<(T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>)> where T: 'static {
    match ls {
    loops_rec_List_0::Cons(x_0, __rec_1) => (if (i == 0u32) { Ok((x_0, (Box::new(move |v2: T| -> loops_rec_List_0<T> { loops_rec_List_0::Cons(v2, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>))) } else { {
    let i_3: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (v4, back_5): (T, Box<dyn FnOnce(T) -> loops_rec_List_0<T>>) = (loops_rec_list_nth_mut_7_loop0::<T>((*__rec_1), i_3))?;
    let back_6: Box<dyn FnOnce(T) -> loops_rec_List_0<T>> = (Box::new(move |v7: T| -> loops_rec_List_0<T> { {
    let v8: loops_rec_List_0<T> = (back_5(v7));
    loops_rec_List_0::Cons(x_0, Box::new(v8))
} }) as Box<dyn FnOnce(T) -> loops_rec_List_0<T>>);
    Ok((v4, back_6))
} }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_list_nth_shared_8_loop0<T>(ls: loops_rec_List_0<T>, i: u32) -> Result<T> where T: 'static {
    match ls {
    loops_rec_List_0::Cons(x_0, __rec_1) => (if (i == 0u32) { Ok(x_0) } else { {
    let i_2: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (loops_rec_list_nth_shared_8_loop0::<T>((*__rec_1), i_2))
} }),
    loops_rec_List_0::Nil => Err(()),
}
}

pub fn loops_rec_sum_array_4_loop0<const N: usize>(a: [u32; N], i: usize, s: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_iter_local_mut_borrow_34_loop0(p: i32) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_reborrow_const_37_loop0() -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_issue500_2_27_loop0() -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_iter_local_shared_borrow_35_loop0() -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_issue500_1_26_loop0(a: bool) -> Result<bool> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_issue351_29_loop0(t: loops_rec_List_0<u8>, last: u8) -> Result<u8> {
    match t {
    loops_rec_List_0::Cons(ht_0, __rec_1) => (loops_rec_issue351_29_loop0((*__rec_1), ht_0)),
    loops_rec_List_0::Nil => Ok(last),
}
}

pub fn loops_rec_iter_0_loop0(max: u32, i: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_incr_ignore_input_mut_borrow_24_loop0(i: u32) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_issue500_3_28_loop0() -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_ignore_input_mut_borrow_23_loop0(i: u32) -> Result<()> {
    panic!("LoopOp placeholder")
}

pub fn loops_rec_ignore_input_shared_borrow_25_loop0(i: u32) -> Result<()> {
    panic!("LoopOp placeholder")
}

