
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

pub enum rename_attribute_SimpleEnum_1 {
    FirstVariant,
    SecondVariant,
    ThirdVariant,
}

pub struct rename_attribute_Foo_2 {
    pub field1: u32,
}

pub fn rename_attribute_BoolTrait_get_bool_3<Self_>(p0: impl core::marker::Sized) -> Result<bool> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn rename_attribute_sum_2(max: u32) -> Result<u32> {
    let s_0: u32 = (rename_attribute_sum_2_loop0(max, 0u32, 0u32))?;
    (s_0.checked_mul(2u32).ok_or(()))
}

pub fn rename_attribute_factorial_1(n: u64) -> Result<u64> {
    (if (n <= 1u64) { Ok(1u64) } else { {
    let v0: u64 = (n.checked_sub(1u64).ok_or(()))?;
    let v1: u64 = (rename_attribute_factorial_1(v0))?;
    (n.checked_mul(v1).ok_or(()))
} })
}

pub fn rename_attribute_test_bool_trait_0<T>(x: bool) -> Result<bool> where T: 'static {
    let v0: bool = (impl_rename_attribute_get_bool_5(x))?;
    (if v0 { (impl_rename_attribute_ret_true_6(x)) } else { Ok(false) })
}

pub fn rename_attribute_C_7() -> Result<u32> {
    let v0: u32 = (100u32.checked_add(10u32).ok_or(()))?;
    (v0.checked_add(1u32).ok_or(()))
}

pub fn rename_attribute_CA_8() -> Result<u32> {
    (10u32.checked_add(1u32).ok_or(()))
}

pub fn rename_attribute_BoolTrait_ret_true_4<Self_>(self_: Self_) -> Result<bool> where Self_: 'static {
    Ok(true)
}

pub fn impl_rename_attribute_get_bool_5(self_: bool) -> Result<bool> {
    Ok(self_)
}

pub fn impl_rename_attribute_ret_true_6(self_: bool) -> Result<bool> {
    Ok(true)
}

pub fn rename_attribute_sum_2_loop0(max: u32, i: u32, s: u32) -> Result<u32> {
    panic!("LoopOp placeholder")
}

