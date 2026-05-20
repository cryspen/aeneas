
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

pub struct constants_lean_Wrapper_0<const N: usize, const M: usize>([u8; N], [u8; N]);

pub fn impl_core_cmp_impls_eq_1<A, B>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where A: 'static, B: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_7<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_9(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn constants_lean_use_params_0<P>(n: usize) -> Result<bool> where P: 'static {
    let v0: usize = (Err::<usize, ()>(()))?;
    let v1: usize = (Err::<usize, ()>(()))?;
    let v2: usize = (v0.checked_mul(v1).ok_or(()))?;
    Ok((impl_core_cmp_impls_eq_9(n, v2)))
}

pub fn constants_lean_NM_4() -> Result<usize> {
    (0usize.checked_mul(0usize).ok_or(()))
}

pub fn constants_lean_Params1_PACKED_LEN_16<Self_>() -> Result<usize> where Self_: 'static {
    let v0: usize = (Err::<usize, ()>(()))?;
    let v1: usize = (Err::<usize, ()>(()))?;
    let v2: usize = (v0.checked_mul(v1).ok_or(()))?;
    (v2.checked_div(8usize).ok_or(()))
}

pub fn impl_constants_lean_NM_11<const N: usize, const M: usize>() -> Result<usize> {
    (0usize.checked_mul(0usize).ok_or(()))
}

pub fn impl_constants_lean_NM_12<const N: usize, const M: usize>() -> Result<usize> {
    (0usize.checked_mul(0usize).ok_or(()))
}

pub fn constants_lean_Trait1_NM_13<Self_>() -> Result<usize> where Self_: 'static {
    let v0: usize = (Err::<usize, ()>(()))?;
    let v1: usize = (Err::<usize, ()>(()))?;
    (v0.checked_mul(v1).ok_or(()))
}

pub fn constants_lean_N_2() -> usize {
    3usize
}

pub fn constants_lean_M_3() -> usize {
    4usize
}

pub fn impl_constants_lean_N_14() -> usize {
    0usize
}

pub fn impl_constants_lean_M_15() -> usize {
    1usize
}

pub fn constants_lean_Params1_CT1_LEN_17<Self_>() -> Result<usize> where Self_: 'static {
    unimplemented!("placeholder")
}

