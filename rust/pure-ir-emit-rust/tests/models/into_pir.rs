
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

pub enum core_result_Result_0<T, E> {
    Ok(T),
    Err(E),
}

// TODO: opaque type core_array_TryFromSliceError_1 — emitting marker struct.
pub struct core_array_TryFromSliceError_1;

// TODO: opaque type core_fmt_Formatter_3 — emitting marker struct.
pub struct core_fmt_Formatter_3;

pub struct core_fmt_Error_4;

pub fn impl_core_result_unwrap_3<T, E>(p0: impl core::marker::Sized) -> Result<T> where T: 'static, E: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_result_expect_4<T, E>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<T> where T: 'static, E: 'static {
    unimplemented!("opaque body")
}

pub fn core_convert_TryFrom_try_from_5<Self_, T, Clause0_Error>(p0: impl core::marker::Sized) -> Result<core_result_Result_0<Self_, Clause0_Error>> where Self_: 'static, T: 'static, Clause0_Error: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_array_try_from_6<T, const N: usize>(p0: impl core::marker::Sized) -> Result<core_result_Result_0<[T; N], core_array_TryFromSliceError_1>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_fmt_Debug_fmt_7<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_0<(), core_fmt_Error_4>, core_fmt_Formatter_3)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_array_fmt_8(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_0<(), core_fmt_Error_4>, core_fmt_Formatter_3)> {
    unimplemented!("opaque body")
}

pub fn into_slice_to_array1_1(s: Vec<u8>) -> Result<[u8; 32usize]> {
    let v0: core_result_Result_0<[u8; 32usize], core_array_TryFromSliceError_1> = (impl_core_array_try_from_6::<u8, 32usize>(s))?;
    (impl_core_result_expect_4::<[u8; 32usize], core_array_TryFromSliceError_1>(v0, "Expected a slice of length 32"))
}

pub fn into_slice_to_array_0(s: Vec<u8>) -> Result<[u8; 32usize]> {
    let v0: core_result_Result_0<[u8; 32usize], core_array_TryFromSliceError_1> = (impl_core_array_try_from_6::<u8, 32usize>(s))?;
    (impl_core_result_unwrap_3::<[u8; 32usize], core_array_TryFromSliceError_1>(v0))
}

