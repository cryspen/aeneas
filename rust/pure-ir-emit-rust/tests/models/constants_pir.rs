
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

pub struct constants_Pair_0<T1, T2> {
    pub x: T1,
    pub y: T2,
}

pub struct constants_Wrap_1<T> {
    pub value: T,
}

pub struct constants_V_2<T, const N: usize> {
    pub x: [T; N],
}

pub fn impl_core_num_MAX_28() -> Result<u32> {
    unimplemented!("opaque body")
}

pub fn constants_get_z2_6() -> Result<i32> {
    let v0: i32 = (constants_get_z1_4())?;
    let v1: i32 = (Err::<i32, ()>(()))?;
    let v2: i32 = (constants_add_5(v0, v1))?;
    (constants_add_5(0i32, v2))
}

pub fn constants_S2_23() -> Result<u32> {
    (constants_incr_0(0u32))
}

pub fn constants_add_5(a: i32, b: i32) -> Result<i32> {
    (a.checked_add(b).ok_or(()))
}

pub fn constants_mk_pair0_1(x: u32, y: u32) -> Result<(u32, u32)> {
    Ok((x, y))
}

pub fn constants_mk_pair1_2(x: u32, y: u32) -> Result<constants_Pair_0<u32, u32>> {
    Ok(constants_Pair_0 { x: x, y: y })
}

pub fn constants_incr_0(n: u32) -> Result<u32> {
    (n.checked_add(1u32).ok_or(()))
}

pub fn constants_unwrap_y_3() -> Result<i32> {
    let v0: constants_Wrap_1<i32> = (Err::<constants_Wrap_1<i32>, ()>(()))?;
    Ok(v0.value)
}

pub fn constants_X2_10() -> u32 {
    3u32
}

pub fn impl_constants_new_18<T>(value: T) -> Result<constants_Wrap_1<T>> where T: 'static {
    Ok(constants_Wrap_1 { value: value })
}

pub fn constants_get_z1_4() -> Result<i32> {
    Ok(0i32)
}

pub fn constants_use_v_7<T, const N: usize>() -> Result<usize> where T: 'static {
    Ok(0usize)
}

pub fn constants_X1_9() -> u32 {
    0u32
}

pub fn constants_Q2_20() -> i32 {
    0i32
}

pub fn constants_Q3_21() -> Result<i32> {
    (constants_add_5(0i32, 3i32))
}

pub fn constants_S3_24() -> constants_Pair_0<u32, u32> {
    unimplemented!("placeholder")
}

pub fn constants_X0_8() -> u32 {
    0u32
}

pub fn constants_X3_11() -> Result<u32> {
    (constants_incr_0(32u32))
}

pub fn constants_P0_12() -> Result<(u32, u32)> {
    (constants_mk_pair0_1(0u32, 1u32))
}

pub fn constants_P1_13() -> Result<constants_Pair_0<u32, u32>> {
    (constants_mk_pair1_2(0u32, 1u32))
}

pub fn constants_P2_14() -> (u32, u32) {
    (0u32, 1u32)
}

pub fn constants_P3_15() -> constants_Pair_0<u32, u32> {
    constants_Pair_0 { x: 0u32, y: 1u32 }
}

pub fn constants_Y_16() -> Result<constants_Wrap_1<i32>> {
    (impl_constants_new_18::<i32>(2i32))
}

pub fn constants_YVAL_17() -> Result<i32> {
    (constants_unwrap_y_3())
}

pub fn constants_Q1_19() -> i32 {
    5i32
}

pub fn constants_S1_22() -> u32 {
    6u32
}

pub fn constants_S4_25() -> Result<constants_Pair_0<u32, u32>> {
    (constants_mk_pair1_2(7u32, 8u32))
}

pub fn constants_get_z1_Z1_26() -> i32 {
    3i32
}

pub fn impl_constants_LEN_27<T, const N: usize>() -> usize where T: 'static {
    0usize
}

