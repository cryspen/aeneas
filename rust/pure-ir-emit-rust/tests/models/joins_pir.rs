
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

pub enum joins_Enum_0 {
    V0,
    V1,
    V2,
}

pub fn joins_opt_add_2_1(b: bool, x: u32) -> Result<u32> {
    let y_0: u32 = (if b { Ok(1u32) } else { Ok(0u32) })?;
    let z_1: u32 = (if b { Ok(1u32) } else { Ok(0u32) })?;
    let v2: u32 = (x.checked_add(y_0).ok_or(()))?;
    (v2.checked_add(z_1).ok_or(()))
}

pub fn joins_call_choose_6(b: bool, x: u32, y: u32) -> Result<(u32, u32)> {
    let (z_0, back_1): (u32, Box<dyn FnOnce(u32) -> (u32, u32)>) = (if b { Ok((x, (Box::new(move |v2: u32| -> (u32, u32) { (v2, y) }) as Box<dyn FnOnce(u32) -> (u32, u32)>))) } else { Ok((y, (Box::new(move |v3: u32| -> (u32, u32) { (x, v3) }) as Box<dyn FnOnce(u32) -> (u32, u32)>))) })?;
    let z_4: u32 = (z_0.checked_add(1u32).ok_or(()))?;
    Ok((back_1(z_4)))
}

pub fn joins_opt_add_1_0(b: bool, x: u32) -> Result<u32> {
    let y_0: u32 = (if b { Ok(1u32) } else { Ok(0u32) })?;
    (x.checked_add(y_0).ok_or(()))
}

pub fn joins_opt_add_switch_1_3(a: u32, x: u32) -> Result<u32> {
    let y_0: u32 = match a {
    0u32 => Ok(0u32),
    1u32 => Ok(1u32),
    _ => Err(()),
}?;
    (x.checked_add(y_0).ok_or(()))
}

pub fn joins_use_enum_5(e: joins_Enum_0, x: u32) -> Result<u32> {
    let y_0: u32 = match e {
    joins_Enum_0::V0 => Ok(0u32),
    joins_Enum_0::V1 => Ok(1u32),
    joins_Enum_0::V2 => Ok(2u32),
}?;
    (x.checked_add(y_0).ok_or(()))
}

pub fn joins_opt_add_switch_2_4(a: u32, x: u32) -> Result<u32> {
    match a {
    0u32 => (x.checked_add(0u32).ok_or(())),
    _ => Err(()),
}
}

pub fn joins_opt_add_1_or_panic_2(b: bool, x: u32) -> Result<u32> {
    let _: () = (if b { Ok(()) } else { Err(()) })?;
    (x.checked_add(1u32).ok_or(()))
}

