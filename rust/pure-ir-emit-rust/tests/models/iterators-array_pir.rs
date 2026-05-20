
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

// TODO: opaque type alloc_vec_into_iter_IntoIter_2 — emitting marker struct.
pub struct alloc_vec_into_iter_IntoIter_2<T, A>(pub core::marker::PhantomData<fn() -> (T, A,)>);

pub enum core_option_Option_3<T> {
    None,
    Some(T),
}

pub fn impl_alloc_vec_from_1<T, const N: usize>(p0: impl core::marker::Sized) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_into_iter_2<T, A>(p0: impl core::marker::Sized) -> Result<alloc_vec_into_iter_IntoIter_2<T, A>> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_into_iter_next_4<T, A>(p0: impl core::marker::Sized) -> Result<(core_option_Option_3<T>, alloc_vec_into_iter_IntoIter_2<T, A>)> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn iterators_array_iter_array_0() -> Result<()> {
    let v_0: alloc_vec_Vec_0<u32> = (impl_alloc_vec_from_1::<u32, 3usize>([1u32, 2u32, 3u32]))?;
    let iter_1: alloc_vec_into_iter_IntoIter_2<u32, alloc_alloc_Global_1> = (impl_alloc_vec_into_iter_2::<u32, alloc_alloc_Global_1>(v_0))?;
    (iterators_array_iter_array_0_loop0(iter_1, 0i32))
}

pub fn iterators_array_iter_array_0_loop0(iter: alloc_vec_into_iter_IntoIter_2<u32, alloc_alloc_Global_1>, x: i32) -> Result<()> {
    panic!("LoopOp placeholder")
}

