
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

pub fn impl_core_array_clone_3<T, const N: usize>(p0: impl core::marker::Sized) -> Result<[T; N]> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_4<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn arrays_defs_index_empty_array_2() -> Result<()> {
    let v0: Vec<u32> = Ok(unimplemented!("FBuiltin call"))?;
    let _: u32 = (arrays_defs_index_slice_0_1::<u32>(v0))?;
    Ok(())
}

pub fn arrays_defs_index_slice_0_1<T>(s: Vec<T>) -> Result<T> where T: 'static {
    unimplemented!("FBuiltin call")
}

pub fn arrays_defs_clone_array_0<T, const N: usize>(x: [T; N]) -> Result<[T; N]> where T: 'static {
    (impl_core_array_clone_3::<T, N>(x))
}

