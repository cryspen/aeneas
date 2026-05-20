
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

// TODO: opaque type core_fmt_Formatter_1 — emitting marker struct.
pub struct core_fmt_Formatter_1;

pub enum core_result_Result_2<T, E> {
    Ok(T),
    Err(E),
}

pub struct core_fmt_Error_3;

pub fn impl_core_clone_impls_clone_9(p0: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_10(p0: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn impl_core_convert_into_11<T, U>(p0: impl core::marker::Sized) -> Result<U> where T: 'static, U: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_convert_from_13<T>(p0: impl core::marker::Sized) -> T where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_num_from_le_bytes_14(p0: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn impl_core_num_to_le_bytes_15(p0: impl core::marker::Sized) -> [u8; 4usize] {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_17<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_convert_From_from_20<Self_, T>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static, T: 'static {
    unimplemented!("opaque body")
}

pub fn core_fmt_Debug_fmt_21<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_2<(), core_fmt_Error_3>, core_fmt_Formatter_1)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn builtin_into_from_2<T, U>(x: T) -> Result<U> where T: 'static, U: 'static {
    (impl_core_convert_into_11::<T, U>(x))
}

pub fn builtin_into_same_3<T>(x: T) -> Result<T> where T: 'static {
    (impl_core_convert_into_11::<T, T>(x))
}

pub fn builtin_from_same_4<T>(x: T) -> Result<T> where T: 'static {
    Ok((impl_core_convert_from_13::<T>(x)))
}

pub fn builtin_clone_bool_0(x: bool) -> Result<bool> {
    Ok((impl_core_clone_impls_clone_9(x)))
}

pub fn builtin_clone_u32_1(x: u32) -> Result<u32> {
    Ok((impl_core_clone_impls_clone_10(x)))
}

pub fn builtin_u32_from_le_bytes_6(x: [u8; 4usize]) -> Result<u32> {
    Ok((impl_core_num_from_le_bytes_14(x)))
}

pub fn builtin_u32_to_le_bytes_7(x: u32) -> Result<[u8; 4usize]> {
    Ok((impl_core_num_to_le_bytes_15(x)))
}

pub fn builtin_use_debug_clause_8<T>(p0: T) -> Result<()> where T: 'static {
    Ok(())
}

pub fn builtin_copy_5<T>(x: T) -> Result<T> where T: 'static {
    Ok(x)
}

