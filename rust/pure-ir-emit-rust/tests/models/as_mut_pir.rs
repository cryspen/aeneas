
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

pub fn impl_alloc_boxed_as_mut_2<T, A>(p0: impl core::marker::Sized) -> (T, Box<dyn FnOnce(T) -> T>) where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn core_convert_AsMut_as_mut_3<Self_, T>(p0: impl core::marker::Sized) -> Result<(T, Box<dyn FnOnce(T) -> Self_>)> where Self_: 'static, T: 'static {
    unimplemented!("opaque body")
}

pub fn as_mut_use_box_as_mut_0<T>(x: T) -> Result<(T, Box<dyn FnOnce(T) -> T>)> where T: 'static {
    Ok((impl_alloc_boxed_as_mut_2::<T, alloc_alloc_Global_0>(x)))
}

pub fn as_mut_use_as_mut_1<S, T>(x: T) -> Result<(S, Box<dyn FnOnce(S) -> T>)> where S: 'static, T: 'static {
    unimplemented!("TraitMethod")
}

