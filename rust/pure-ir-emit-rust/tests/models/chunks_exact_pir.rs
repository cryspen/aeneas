
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

// TODO: opaque type core_slice_iter_ChunksExact_0 — emitting marker struct.
pub struct core_slice_iter_ChunksExact_0<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub enum core_option_Option_1<T> {
    None,
    Some(T),
}

pub fn impl_core_slice_chunks_exact_9<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_slice_iter_ChunksExact_0<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_next_10<T>(p0: impl core::marker::Sized) -> Result<(core_option_Option_1<Vec<T>>, core_slice_iter_ChunksExact_0<T>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_unwrap_11<T>(p0: impl core::marker::Sized) -> Result<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_is_none_12<T>(p0: impl core::marker::Sized) -> bool where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_remainder_13<T>(p0: impl core::marker::Sized) -> Result<Vec<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_len_14<T>(p0: impl core::marker::Sized) -> usize where T: 'static {
    unimplemented!("opaque body")
}

pub fn chunks_exact_test_chunks_exact_with_remainder_1() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 3usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c1_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 1u32) { Ok(()) } else { Err(()) })?;
    let v6: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v6 == 2u32) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v7 == 3u32) { Ok(()) } else { Err(()) })?;
    let (v8, it_9): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let c2_10: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v8))?;
    let v11: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v11 == 4u32) { Ok(()) } else { Err(()) })?;
    let v12: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v12 == 5u32) { Ok(()) } else { Err(()) })?;
    let v13: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v13 == 6u32) { Ok(()) } else { Err(()) })?;
    let (v14, it_15): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_9))?;
    let v16: bool = (impl_core_option_is_none_12::<Vec<u32>>(v14));
    let _: () = (if v16 { Ok(()) } else { Err(()) })?;
    let rem_17: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_15))?;
    let v18: usize = (impl_core_slice_len_14::<u32>(rem_17));
    let _: () = (if (v18 == 1usize) { Ok(()) } else { Err(()) })?;
    let v19: u32 = (Err::<u32, ()>(()))?;
    (if (v19 == 7u32) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_exact_fit_0() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 3usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c1_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 1u32) { Ok(()) } else { Err(()) })?;
    let v6: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v6 == 2u32) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v7 == 3u32) { Ok(()) } else { Err(()) })?;
    let (v8, it_9): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let c2_10: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v8))?;
    let v11: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v11 == 4u32) { Ok(()) } else { Err(()) })?;
    let v12: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v12 == 5u32) { Ok(()) } else { Err(()) })?;
    let v13: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v13 == 6u32) { Ok(()) } else { Err(()) })?;
    let (v14, it_15): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_9))?;
    let v16: bool = (impl_core_option_is_none_12::<Vec<u32>>(v14));
    let _: () = (if v16 { Ok(()) } else { Err(()) })?;
    let rem_17: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_15))?;
    let v18: usize = (impl_core_slice_len_14::<u32>(rem_17));
    (if (v18 == 0usize) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_2_odd_7() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 2usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c1_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 1u32) { Ok(()) } else { Err(()) })?;
    let v6: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v6 == 2u32) { Ok(()) } else { Err(()) })?;
    let (v7, it_8): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let c2_9: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v7))?;
    let v10: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v10 == 3u32) { Ok(()) } else { Err(()) })?;
    let v11: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v11 == 4u32) { Ok(()) } else { Err(()) })?;
    let (v12, it_13): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_8))?;
    let v14: bool = (impl_core_option_is_none_12::<Vec<u32>>(v12));
    let _: () = (if v14 { Ok(()) } else { Err(()) })?;
    let rem_15: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_13))?;
    let v16: usize = (impl_core_slice_len_14::<u32>(rem_15));
    let _: () = (if (v16 == 1usize) { Ok(()) } else { Err(()) })?;
    let v17: u32 = (Err::<u32, ()>(()))?;
    (if (v17 == 5u32) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_remainder_2_2() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 3usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 10u32) { Ok(()) } else { Err(()) })?;
    let v6: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v6 == 20u32) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v7 == 30u32) { Ok(()) } else { Err(()) })?;
    let (v8, it_9): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let v10: bool = (impl_core_option_is_none_12::<Vec<u32>>(v8));
    let _: () = (if v10 { Ok(()) } else { Err(()) })?;
    let rem_11: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_9))?;
    let v12: usize = (impl_core_slice_len_14::<u32>(rem_11));
    let _: () = (if (v12 == 2usize) { Ok(()) } else { Err(()) })?;
    let v13: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v13 == 40u32) { Ok(()) } else { Err(()) })?;
    let v14: u32 = (Err::<u32, ()>(()))?;
    (if (v14 == 50u32) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_size_1_3() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 1usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c1_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 10u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let c2_8: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v6))?;
    let v9: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v9 == 20u32) { Ok(()) } else { Err(()) })?;
    let (v10, it_11): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_7))?;
    let c3_12: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v10))?;
    let v13: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v13 == 30u32) { Ok(()) } else { Err(()) })?;
    let (v14, it_15): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_11))?;
    let v16: bool = (impl_core_option_is_none_12::<Vec<u32>>(v14));
    let _: () = (if v16 { Ok(()) } else { Err(()) })?;
    let rem_17: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_15))?;
    let v18: usize = (impl_core_slice_len_14::<u32>(rem_17));
    (if (v18 == 0usize) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_chunk_equals_slice_6() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 3usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let c_4: Vec<u32> = (impl_core_option_unwrap_11::<Vec<u32>>(v2))?;
    let v5: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v5 == 1u32) { Ok(()) } else { Err(()) })?;
    let v6: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v6 == 2u32) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v7 == 3u32) { Ok(()) } else { Err(()) })?;
    let (v8, it_9): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_3))?;
    let v10: bool = (impl_core_option_is_none_12::<Vec<u32>>(v8));
    let _: () = (if v10 { Ok(()) } else { Err(()) })?;
    let rem_11: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_9))?;
    let v12: usize = (impl_core_slice_len_14::<u32>(rem_11));
    (if (v12 == 0usize) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_chunk_larger_than_slice_5() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 5usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let v4: bool = (impl_core_option_is_none_12::<Vec<u32>>(v2));
    let _: () = (if v4 { Ok(()) } else { Err(()) })?;
    let rem_5: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_3))?;
    let v6: usize = (impl_core_slice_len_14::<u32>(rem_5));
    let _: () = (if (v6 == 2usize) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    let _: () = (if (v7 == 1u32) { Ok(()) } else { Err(()) })?;
    let v8: u32 = (Err::<u32, ()>(()))?;
    (if (v8 == 2u32) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_2_single_element_8() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 2usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let v4: bool = (impl_core_option_is_none_12::<Vec<u32>>(v2));
    let _: () = (if v4 { Ok(()) } else { Err(()) })?;
    let rem_5: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_3))?;
    let v6: usize = (impl_core_slice_len_14::<u32>(rem_5));
    let _: () = (if (v6 == 1usize) { Ok(()) } else { Err(()) })?;
    let v7: u32 = (Err::<u32, ()>(()))?;
    (if (v7 == 42u32) { Ok(()) } else { Err(()) })
}

pub fn chunks_exact_test_chunks_exact_empty_4() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let it_1: core_slice_iter_ChunksExact_0<u32> = (impl_core_slice_chunks_exact_9::<u32>(v0, 3usize))?;
    let (v2, it_3): (core_option_Option_1<Vec<u32>>, core_slice_iter_ChunksExact_0<u32>) = (impl_core_slice_iter_next_10::<u32>(it_1))?;
    let v4: bool = (impl_core_option_is_none_12::<Vec<u32>>(v2));
    let _: () = (if v4 { Ok(()) } else { Err(()) })?;
    let rem_5: Vec<u32> = (impl_core_slice_iter_remainder_13::<u32>(it_3))?;
    let v6: usize = (impl_core_slice_len_14::<u32>(rem_5));
    (if (v6 == 0usize) { Ok(()) } else { Err(()) })
}

