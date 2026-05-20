
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

pub struct alloc_alloc_Global_0;

// TODO: opaque type alloc_vec_Vec_1 — emitting marker struct.
pub struct alloc_vec_Vec_1<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub fn impl_alloc_boxed_deref_5<T, A>(p0: impl core::marker::Sized) -> T where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_boxed_deref_mut_6<T, A>(p0: impl core::marker::Sized) -> (T, Box<dyn FnOnce(T) -> T>) where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_deref_8<T, A>(p0: impl core::marker::Sized) -> Vec<T> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_deref_mut_9<T, A>(p0: impl core::marker::Sized) -> (Vec<T>, Box<dyn FnOnce(Vec<T>) -> alloc_vec_Vec_1<T>>) where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn deref_test_deref_box_2() -> Result<()> {
    let (_, deref_mut_back_0): (i32, Box<dyn FnOnce(i32) -> i32>) = Ok((impl_alloc_boxed_deref_mut_6::<i32, alloc_alloc_Global_0>(0i32)))?;
    let b_1: i32 = (deref_mut_back_0(1i32));
    let x_2: i32 = Ok((impl_alloc_boxed_deref_5::<i32, alloc_alloc_Global_0>(b_1)))?;
    (if (x_2 == 1i32) { Ok(()) } else { Err(()) })
}

pub fn deref_use_deref_mut_box_1<T>(x: T) -> Result<(T, Box<dyn FnOnce(T) -> T>)> where T: 'static {
    Ok((impl_alloc_boxed_deref_mut_6::<T, alloc_alloc_Global_0>(x)))
}

pub fn deref_use_deref_mut_vec_4<T>(x: alloc_vec_Vec_1<T>) -> Result<(Vec<T>, Box<dyn FnOnce(Vec<T>) -> alloc_vec_Vec_1<T>>)> where T: 'static {
    Ok((impl_alloc_vec_deref_mut_9::<T, alloc_alloc_Global_0>(x)))
}

pub fn deref_use_deref_box_0<T>(x: T) -> Result<T> where T: 'static {
    Ok((impl_alloc_boxed_deref_5::<T, alloc_alloc_Global_0>(x)))
}

pub fn deref_use_deref_vec_3<T>(x: alloc_vec_Vec_1<T>) -> Result<Vec<T>> where T: 'static {
    Ok((impl_alloc_vec_deref_8::<T, alloc_alloc_Global_0>(x)))
}

