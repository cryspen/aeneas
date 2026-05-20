
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

pub enum demo_CList_0<T> {
    CCons(T, Box<demo_CList_0<T>>),
    CNil,
}

pub fn demo_Counter_incr_12<Self_>(p0: impl core::marker::Sized) -> Result<(usize, Self_)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_num_wrapping_sub_14(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn impl_core_num_wrapping_add_15(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn demo_list_nth_mut_7<T>(l: demo_CList_0<T>, i: u32) -> Result<(T, Box<dyn FnOnce(T) -> demo_CList_0<T>>)> where T: 'static {
    match l {
    demo_CList_0::CCons(x_0, __rec_1) => (if (i == 0u32) { {
    let back_2: Box<dyn FnOnce(T) -> demo_CList_0<T>> = (Box::new(move |v3: T| -> demo_CList_0<T> { demo_CList_0::CCons(v3, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> demo_CList_0<T>>);
    Ok((x_0, back_2))
} } else { {
    let v4: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (x_5, list_nth_mut_back_6): (T, Box<dyn FnOnce(T) -> demo_CList_0<T>>) = (demo_list_nth_mut_7::<T>((*__rec_1), v4))?;
    let back_7: Box<dyn FnOnce(T) -> demo_CList_0<T>> = (Box::new(move |v8: T| -> demo_CList_0<T> { {
    let tl_9: demo_CList_0<T> = (list_nth_mut_back_6(v8));
    demo_CList_0::CCons(x_0, Box::new(tl_9))
} }) as Box<dyn FnOnce(T) -> demo_CList_0<T>>);
    Ok((x_5, back_7))
} }),
    demo_CList_0::CNil => Err(()),
}
}

pub fn demo_mod_add_11(a: u32, b: u32) -> Result<u32> {
    let _: () = (if (a < 3329u32) { Ok(()) } else { Err(()) })?;
    let _: () = (if (b < 3329u32) { Ok(()) } else { Err(()) })?;
    let sum_0: u32 = (a.checked_add(b).ok_or(()))?;
    let res_1: u32 = Ok((impl_core_num_wrapping_sub_14(sum_0, 3329u32)))?;
    let mask_2: u32 = (res_1.checked_shr((16i32) as u32).ok_or(()))?;
    let q_3: u32 = Ok((3329u32 & mask_2))?;
    Ok((impl_core_num_wrapping_add_15(res_1, q_3)))
}

pub fn demo_list_nth_5<T>(l: demo_CList_0<T>, i: u32) -> Result<T> where T: 'static {
    match l {
    demo_CList_0::CCons(x_0, __rec_1) => (if (i == 0u32) { Ok(x_0) } else { {
    let v2: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (demo_list_nth_5::<T>((*__rec_1), v2))
} }),
    demo_CList_0::CNil => Err(()),
}
}

pub fn demo_list_nth1_6<T>(l: demo_CList_0<T>, i: u32) -> Result<T> where T: 'static {
    (demo_list_nth1_6_loop0::<T>(l, i))
}

pub fn demo_use_incr_4() -> Result<()> {
    let x_0: u32 = (demo_incr_3(0u32))?;
    let x_1: u32 = (demo_incr_3(x_0))?;
    let _: u32 = (demo_incr_3(x_1))?;
    Ok(())
}

pub fn demo_i32_id_8(i: i32) -> Result<i32> {
    (if (i == 0i32) { Ok(0i32) } else { {
    let v0: i32 = (i.checked_sub(1i32).ok_or(()))?;
    let v1: i32 = (demo_i32_id_8(v0))?;
    (v1.checked_add(1i32).ok_or(()))
} })
}

pub fn demo_list_tail_9<T>(l: demo_CList_0<T>) -> Result<(demo_CList_0<T>, Box<dyn FnOnce(demo_CList_0<T>) -> demo_CList_0<T>>)> where T: 'static {
    match l {
    demo_CList_0::CCons(v0, __rec_1) => {
    let (v2, list_tail_back_3): (demo_CList_0<T>, Box<dyn FnOnce(demo_CList_0<T>) -> demo_CList_0<T>>) = (demo_list_tail_9::<T>((*__rec_1)))?;
    let back_4: Box<dyn FnOnce(demo_CList_0<T>) -> demo_CList_0<T>> = (Box::new(move |v5: demo_CList_0<T>| -> demo_CList_0<T> { {
    let tl_6: demo_CList_0<T> = (list_tail_back_3(v5));
    demo_CList_0::CCons(v0, Box::new(tl_6))
} }) as Box<dyn FnOnce(demo_CList_0<T>) -> demo_CList_0<T>>);
    Ok((v2, back_4))
},
    demo_CList_0::CNil => Ok((demo_CList_0::<T>::CNil, (Box::new(move |l_7: demo_CList_0<T>| -> demo_CList_0<T> { l_7 }) as Box<dyn FnOnce(demo_CList_0<T>) -> demo_CList_0<T>>))),
}
}

pub fn demo_choose_0<T>(b: bool, x: T, y: T) -> Result<(T, Box<dyn FnOnce(T) -> (T, T)>)> where T: 'static {
    (if b { {
    let back_0: Box<dyn FnOnce(T) -> (T, T)> = (Box::new(move |x_1: T| -> (T, T) { (x_1, y) }) as Box<dyn FnOnce(T) -> (T, T)>);
    Ok((x, back_0))
} } else { {
    let back_2: Box<dyn FnOnce(T) -> (T, T)> = (Box::new(move |y_3: T| -> (T, T) { (x, y_3) }) as Box<dyn FnOnce(T) -> (T, T)>);
    Ok((y, back_2))
} })
}

pub fn demo_mul2_add1_1(x: u32) -> Result<u32> {
    let v0: u32 = (x.checked_add(x).ok_or(()))?;
    (v0.checked_add(1u32).ok_or(()))
}

pub fn demo_use_mul2_add1_2(x: u32, y: u32) -> Result<u32> {
    let v0: u32 = (demo_mul2_add1_1(x))?;
    (v0.checked_add(y).ok_or(()))
}

pub fn impl_demo_incr_13(self_: usize) -> Result<(usize, usize)> {
    let self_0: usize = (self_.checked_add(1usize).ok_or(()))?;
    Ok((self_, self_0))
}

pub fn demo_incr_3(x: u32) -> Result<u32> {
    (x.checked_add(1u32).ok_or(()))
}

pub fn demo_use_counter_10<T>(cnt: T) -> Result<(usize, T)> where T: 'static {
    unimplemented!("TraitMethod")
}

pub fn demo_list_nth1_6_loop0<T>(l: demo_CList_0<T>, i: u32) -> Result<T> where T: 'static {
    match l {
    demo_CList_0::CCons(x_0, __rec_1) => (if (i == 0u32) { Ok(x_0) } else { {
    let i_2: u32 = (i.checked_sub(1u32).ok_or(()))?;
    (demo_list_nth1_6_loop0::<T>((*__rec_1), i_2))
} }),
    demo_CList_0::CNil => Err(()),
}
}

