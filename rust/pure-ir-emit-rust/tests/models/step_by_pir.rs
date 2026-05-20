
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

// TODO: opaque type core_iter_adapters_step_by_StepBy_0 — emitting marker struct.
pub struct core_iter_adapters_step_by_StepBy_0<I>(pub core::marker::PhantomData<fn() -> (I,)>);

// TODO: opaque type core_slice_iter_Iter_1 — emitting marker struct.
pub struct core_slice_iter_Iter_1<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub enum core_option_Option_2<T> {
    None,
    Some(T),
}

pub fn impl_core_slice_iter_11<T>(p0: impl core::marker::Sized) -> Result<core_slice_iter_Iter_1<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_step_by_12<Self_, Clause0_Item>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_0<Self_>> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_iter_adapters_step_by_next_13<I, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, core_iter_adapters_step_by_StepBy_0<I>)> where I: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_unwrap_14<T>(p0: impl core::marker::Sized) -> Result<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_is_none_15<T>(p0: impl core::marker::Sized) -> bool where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_16<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_next_92<T>(p0: impl core::marker::Sized) -> Result<(core_option_Option_2<T>, core_slice_iter_Iter_1<T>)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_slice_iter_step_by_99<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<T>>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn step_by_test_step_by_1_0() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 1usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v8: u32 = (impl_core_option_unwrap_14::<u32>(v6))?;
    let _: () = (if (v8 == 1u32) { Ok(()) } else { Err(()) })?;
    let (v9, it_10): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_7))?;
    let v11: u32 = (impl_core_option_unwrap_14::<u32>(v9))?;
    let _: () = (if (v11 == 2u32) { Ok(()) } else { Err(()) })?;
    let (v12, it_13): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_10))?;
    let v14: u32 = (impl_core_option_unwrap_14::<u32>(v12))?;
    let _: () = (if (v14 == 3u32) { Ok(()) } else { Err(()) })?;
    let (v15, it_16): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_13))?;
    let v17: u32 = (impl_core_option_unwrap_14::<u32>(v15))?;
    let _: () = (if (v17 == 4u32) { Ok(()) } else { Err(()) })?;
    let (v18, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_16))?;
    let v19: bool = (impl_core_option_is_none_15::<u32>(v18));
    (if v19 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_2_1() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 2usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v8: u32 = (impl_core_option_unwrap_14::<u32>(v6))?;
    let _: () = (if (v8 == 2u32) { Ok(()) } else { Err(()) })?;
    let (v9, it_10): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_7))?;
    let v11: u32 = (impl_core_option_unwrap_14::<u32>(v9))?;
    let _: () = (if (v11 == 4u32) { Ok(()) } else { Err(()) })?;
    let (v12, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_10))?;
    let v13: bool = (impl_core_option_is_none_15::<u32>(v12));
    (if v13 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_3_2() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 3usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v8: u32 = (impl_core_option_unwrap_14::<u32>(v6))?;
    let _: () = (if (v8 == 3u32) { Ok(()) } else { Err(()) })?;
    let (v9, it_10): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_7))?;
    let v11: u32 = (impl_core_option_unwrap_14::<u32>(v9))?;
    let _: () = (if (v11 == 6u32) { Ok(()) } else { Err(()) })?;
    let (v12, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_10))?;
    let v13: bool = (impl_core_option_is_none_15::<u32>(v12));
    (if v13 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_4_on_longer_10() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 4usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v8: u32 = (impl_core_option_unwrap_14::<u32>(v6))?;
    let _: () = (if (v8 == 4u32) { Ok(()) } else { Err(()) })?;
    let (v9, it_10): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_7))?;
    let v11: u32 = (impl_core_option_unwrap_14::<u32>(v9))?;
    let _: () = (if (v11 == 8u32) { Ok(()) } else { Err(()) })?;
    let (v12, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_10))?;
    let v13: bool = (impl_core_option_is_none_15::<u32>(v12));
    (if v13 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_len_minus_1_8() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 2usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, it_7): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v8: u32 = (impl_core_option_unwrap_14::<u32>(v6))?;
    let _: () = (if (v8 == 2u32) { Ok(()) } else { Err(()) })?;
    let (v9, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_7))?;
    let v10: bool = (impl_core_option_is_none_15::<u32>(v9));
    (if v10 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_larger_than_len_3() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 10usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v7: bool = (impl_core_option_is_none_15::<u32>(v6));
    (if v7 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_single_5() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 1usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 42u32) { Ok(()) } else { Err(()) })?;
    let (v6, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v7: bool = (impl_core_option_is_none_15::<u32>(v6));
    (if v7 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_single_step_2_6() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 2usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 42u32) { Ok(()) } else { Err(()) })?;
    let (v6, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v7: bool = (impl_core_option_is_none_15::<u32>(v6));
    (if v7 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_eq_len_7() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 3usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v7: bool = (impl_core_option_is_none_15::<u32>(v6));
    (if v7 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_two_elements_9() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 2usize))?;
    let (v3, it_4): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v5: u32 = (impl_core_option_unwrap_14::<u32>(v3))?;
    let _: () = (if (v5 == 0u32) { Ok(()) } else { Err(()) })?;
    let (v6, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_4))?;
    let v7: bool = (impl_core_option_is_none_15::<u32>(v6));
    (if v7 { Ok(()) } else { Err(()) })
}

pub fn step_by_test_step_by_empty_4() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let v1: core_slice_iter_Iter_1<u32> = (impl_core_slice_iter_11::<u32>(v0))?;
    let it_2: core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>> = (impl_core_slice_iter_step_by_99::<u32>(v1, 2usize))?;
    let (v3, _): (core_option_Option_2<u32>, core_iter_adapters_step_by_StepBy_0<core_slice_iter_Iter_1<u32>>) = (impl_core_iter_adapters_step_by_next_13::<core_slice_iter_Iter_1<u32>, u32>(it_2))?;
    let v4: bool = (impl_core_option_is_none_15::<u32>(v3));
    (if v4 { Ok(()) } else { Err(()) })
}

