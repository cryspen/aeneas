
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

pub fn bitwise_shift_u32_0(a: u32) -> Result<u32> {
    let t_0: u32 = (a.checked_shr((16usize) as u32).ok_or(()))?;
    (t_0.checked_shl((16usize) as u32).ok_or(()))
}

pub fn bitwise_shift_i32_1(a: i32) -> Result<i32> {
    let t_0: i32 = (a.checked_shr((16isize) as u32).ok_or(()))?;
    (t_0.checked_shl((16isize) as u32).ok_or(()))
}

pub fn bitwise_xor_u32_2(a: u32, b: u32) -> Result<u32> {
    Ok((a ^ b))
}

pub fn bitwise_or_u32_3(a: u32, b: u32) -> Result<u32> {
    Ok((a | b))
}

pub fn bitwise_and_u32_4(a: u32, b: u32) -> Result<u32> {
    Ok((a & b))
}

