
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

pub enum paper_List_0<T> {
    Cons(T, Box<paper_List_0<T>>),
    Nil,
}

pub struct alloc_alloc_Global_1;

pub fn paper_test_choose_3() -> Result<()> {
    let (z_0, choose_back_1): (i32, Box<dyn FnOnce(i32) -> (i32, i32)>) = (paper_choose_2::<i32>(true, 0i32, 0i32))?;
    let z_2: i32 = (z_0.checked_add(1i32).ok_or(()))?;
    let _: () = (if (z_2 == 1i32) { Ok(()) } else { Err(()) })?;
    let (x_3, y_4): (i32, i32) = (choose_back_1(z_2));
    let _: () = (if (x_3 == 1i32) { Ok(()) } else { Err(()) })?;
    (if (y_4 == 0i32) { Ok(()) } else { Err(()) })
}

pub fn paper_test_nth_6() -> Result<()> {
    let (x_0, list_nth_mut_back_1): (i32, Box<dyn FnOnce(i32) -> paper_List_0<i32>>) = (paper_list_nth_mut_4::<i32>(paper_List_0::Cons(1i32, Box::new(paper_List_0::Cons(2i32, Box::new(paper_List_0::Cons(3i32, Box::new(paper_List_0::<i32>::Nil)))))), 2u32))?;
    let x_2: i32 = (x_0.checked_add(1i32).ok_or(()))?;
    let l_3: paper_List_0<i32> = (list_nth_mut_back_1(x_2));
    let v4: i32 = (paper_sum_5(l_3))?;
    (if (v4 == 7i32) { Ok(()) } else { Err(()) })
}

pub fn paper_list_nth_mut_4<T>(l: paper_List_0<T>, i: u32) -> Result<(T, Box<dyn FnOnce(T) -> paper_List_0<T>>)> where T: 'static {
    match l {
    paper_List_0::Cons(x_0, __rec_1) => (if (i == 0u32) { {
    let back_2: Box<dyn FnOnce(T) -> paper_List_0<T>> = (Box::new(move |v3: T| -> paper_List_0<T> { paper_List_0::Cons(v3, Box::new((*__rec_1))) }) as Box<dyn FnOnce(T) -> paper_List_0<T>>);
    Ok((x_0, back_2))
} } else { {
    let v4: u32 = (i.checked_sub(1u32).ok_or(()))?;
    let (x_5, list_nth_mut_back_6): (T, Box<dyn FnOnce(T) -> paper_List_0<T>>) = (paper_list_nth_mut_4::<T>((*__rec_1), v4))?;
    let back_7: Box<dyn FnOnce(T) -> paper_List_0<T>> = (Box::new(move |v8: T| -> paper_List_0<T> { {
    let tl_9: paper_List_0<T> = (list_nth_mut_back_6(v8));
    paper_List_0::Cons(x_0, Box::new(tl_9))
} }) as Box<dyn FnOnce(T) -> paper_List_0<T>>);
    Ok((x_5, back_7))
} }),
    paper_List_0::Nil => Err(()),
}
}

pub fn paper_test_incr_1() -> Result<()> {
    let x_0: i32 = (paper_ref_incr_0(0i32))?;
    (if (x_0 == 1i32) { Ok(()) } else { Err(()) })
}

pub fn paper_sum_5(l: paper_List_0<i32>) -> Result<i32> {
    match l {
    paper_List_0::Cons(x_0, __rec_1) => {
    let v2: i32 = (paper_sum_5((*__rec_1)))?;
    (x_0.checked_add(v2).ok_or(()))
},
    paper_List_0::Nil => Ok(0i32),
}
}

pub fn paper_call_choose_7(p: (u32, u32)) -> Result<u32> {
    let (px_0, py_1): (u32, u32) = p;
    let (pz_2, choose_back_3): (u32, Box<dyn FnOnce(u32) -> (u32, u32)>) = (paper_choose_2::<u32>(true, px_0, py_1))?;
    let pz_4: u32 = (pz_2.checked_add(1u32).ok_or(()))?;
    let (px_5, _): (u32, u32) = (choose_back_3(pz_4));
    Ok(px_5)
}

pub fn paper_choose_2<T>(b: bool, x: T, y: T) -> Result<(T, Box<dyn FnOnce(T) -> (T, T)>)> where T: 'static {
    (if b { {
    let back_0: Box<dyn FnOnce(T) -> (T, T)> = (Box::new(move |x_1: T| -> (T, T) { (x_1, y) }) as Box<dyn FnOnce(T) -> (T, T)>);
    Ok((x, back_0))
} } else { {
    let back_2: Box<dyn FnOnce(T) -> (T, T)> = (Box::new(move |y_3: T| -> (T, T) { (x, y_3) }) as Box<dyn FnOnce(T) -> (T, T)>);
    Ok((y, back_2))
} })
}

pub fn paper_ref_incr_0(x: i32) -> Result<i32> {
    (x.checked_add(1i32).ok_or(()))
}

