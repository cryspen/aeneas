
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

pub enum core_option_Option_0<T> {
    None,
    Some(T),
}

pub fn impl_core_option_unwrap_or_3<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> T where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_expect_5<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<T> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_option_is_some_6<T>(p0: impl core::marker::Sized) -> bool where T: 'static {
    unimplemented!("opaque body")
}

pub fn options_test_unwrap_or_0<T>(x: core_option_Option_0<T>, default: T) -> Result<T> where T: 'static {
    Ok((impl_core_option_unwrap_or_3::<T>(x, default)))
}

pub fn options_test_expect_1<T>(x: core_option_Option_0<T>, msg: &'static str) -> Result<T> where T: 'static {
    (impl_core_option_expect_5::<T>(x, msg))
}

pub fn options_test_is_some_2<T>(x: core_option_Option_0<T>) -> Result<bool> where T: 'static {
    Ok((impl_core_option_is_some_6::<T>(x)))
}

