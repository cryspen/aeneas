
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

pub struct defaulted_method_NoOverride_0;

pub struct defaulted_method_YesOverride_1;

pub fn defaulted_method_Trait_required_method_2<Self_>(p0: impl core::marker::Sized) -> Result<u32> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_min_15(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> i32 {
    unimplemented!("opaque body")
}

pub fn defaulted_method_main_0() -> Result<()> {
    let _: u32 = (impl_defaulted_method_provided_method_3(defaulted_method_NoOverride_0))?;
    let _: u32 = (impl_defaulted_method_provided_method_5(defaulted_method_YesOverride_1))?;
    let n_0: i32 = Ok((impl_core_cmp_impls_min_15(10i32, 1i32)))?;
    (if (n_0 == 1i32) { Ok(()) } else { Err(()) })
}

pub fn defaulted_method_Trait_provided_method_1<Self_>(self_: Self_) -> Result<u32> where Self_: 'static {
    unimplemented!("TraitMethod")
}

pub fn impl_defaulted_method_provided_method_5(self_: defaulted_method_YesOverride_1) -> Result<u32> {
    (impl_defaulted_method_required_method_6(self_))
}

pub fn impl_defaulted_method_provided_method_3(self_: defaulted_method_NoOverride_0) -> Result<u32> {
    Ok(73u32)
}

pub fn impl_defaulted_method_required_method_4(self_: defaulted_method_NoOverride_0) -> Result<u32> {
    Ok(12u32)
}

pub fn impl_defaulted_method_required_method_6(self_: defaulted_method_YesOverride_1) -> Result<u32> {
    Ok(42u32)
}

