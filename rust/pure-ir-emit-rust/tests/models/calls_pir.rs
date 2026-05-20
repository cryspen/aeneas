
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

pub fn impl_core_num_wrapping_add_5(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn calls_choose_2(b: bool, x: u32, y: u32) -> Result<(u32, Box<dyn FnOnce(u32) -> (u32, u32)>)> {
    (if b { {
    let back_0: Box<dyn FnOnce(u32) -> (u32, u32)> = (Box::new(move |x_1: u32| -> (u32, u32) { (x_1, y) }) as Box<dyn FnOnce(u32) -> (u32, u32)>);
    Ok((x, back_0))
} } else { {
    let back_2: Box<dyn FnOnce(u32) -> (u32, u32)> = (Box::new(move |y_3: u32| -> (u32, u32) { (x, y_3) }) as Box<dyn FnOnce(u32) -> (u32, u32)>);
    Ok((y, back_2))
} })
}

pub fn calls_pick_4(b: bool, x: u32, y: u32) -> Result<u32> {
    let r_0: u32 = (if b { Ok(x) } else { Ok(y) })?;
    Ok((impl_core_num_wrapping_add_5(r_0, 1u32)))
}

pub fn calls_use_choose_3(b: bool, x: u32, y: u32) -> Result<(u32, u32)> {
    let (_, choose_back_0): (u32, Box<dyn FnOnce(u32) -> (u32, u32)>) = (calls_choose_2(b, x, y))?;
    Ok((choose_back_0(7u32)))
}

pub fn calls_incr_via_helper_1(x: u32) -> Result<u32> {
    (calls_incr_inner_0(x))
}

pub fn calls_incr_inner_0(y: u32) -> Result<u32> {
    (y.checked_add(1u32).ok_or(()))
}

