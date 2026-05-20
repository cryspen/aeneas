
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

// TODO: opaque type alloc_vec_Vec_0 — emitting marker struct.
pub struct alloc_vec_Vec_0<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_1;

pub fn impl_alloc_vec_extend_from_slice_3<T, A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<alloc_vec_Vec_0<T>> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_with_capacity_4<T>(p0: impl core::marker::Sized) -> alloc_vec_Vec_0<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn alloc_vec_from_elem_5<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_7<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn vec_use_extend_from_slice_0<T>(v: alloc_vec_Vec_0<T>, s: Vec<T>) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    (impl_alloc_vec_extend_from_slice_3::<T, alloc_alloc_Global_1>(v, s))
}

pub fn vec_from_elem_2<T>(x: T, n: usize) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    (alloc_vec_from_elem_5::<T>(x, n))
}

pub fn vec_use_alloc_with_capacity_1<T>(n: usize) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    Ok((impl_alloc_vec_with_capacity_4::<T>(n)))
}

