
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

pub struct const_shadow_Foo_0;

pub fn const_shadow_HasConst_get_1<Self_, const N: usize>(p0: impl core::marker::Sized) -> Result<[u8; N]> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn const_shadow_use_has_const_0<T, const N: usize>(x: T) -> Result<([u8; N], usize)> where T: 'static {
    let arr_0: [u8; N] = (Err::<[u8; N], ()>(()))?;
    let n_1: usize = (Err::<usize, ()>(()))?;
    Ok((arr_0, n_1))
}

pub fn impl_const_shadow_get_2(self_: const_shadow_Foo_0) -> Result<[u8; 4usize]> {
    Ok(unimplemented!("FBuiltin call"))
}

pub fn impl_const_shadow_N_3() -> usize {
    42usize
}

