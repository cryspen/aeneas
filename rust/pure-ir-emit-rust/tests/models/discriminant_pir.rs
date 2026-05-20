
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

pub enum discriminant_EmptyEnum_0 {
}

pub enum discriminant_AlertLevel_1 {
    Warning,
    Fatal,
}

pub enum discriminant_AlertLevelU8_2 {
    Warning,
    Fatal,
}

pub fn core_cmp_PartialEq_eq_2<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_discriminant_eq_0(self_: discriminant_AlertLevel_1, other: discriminant_AlertLevel_1) -> Result<bool> {
    let self_0: isize = unimplemented!("placeholder");
    let other_1: isize = unimplemented!("placeholder");
    Ok((self_0 == other_1))
}

pub fn impl_discriminant_eq_4(self_: discriminant_AlertLevelU8_2, other: discriminant_AlertLevelU8_2) -> Result<bool> {
    let self_0: u8 = unimplemented!("placeholder");
    let other_1: u8 = unimplemented!("placeholder");
    Ok((self_0 == other_1))
}

