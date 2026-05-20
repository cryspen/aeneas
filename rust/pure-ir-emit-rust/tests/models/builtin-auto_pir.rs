
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

pub struct builtin_auto_Inner_0 {
    pub ptr: *const (),
}

// TODO: opaque type core_fmt_Formatter_3 — emitting marker struct.
pub struct core_fmt_Formatter_3;

pub enum core_result_Result_4<T, E> {
    Ok(T),
    Err(E),
}

pub struct core_fmt_Error_5;

pub enum core_cmp_Ordering_8 {
    Less,
    Equal,
    Greater,
}

pub enum core_option_Option_12<T> {
    None,
    Some(T),
}

pub fn core_ptr_null_1<T>() -> Result<*const ()> where T: 'static {
    unimplemented!("opaque body")
}

pub fn core_fmt_Debug_fmt_2<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_4<(), core_fmt_Error_5>, core_fmt_Formatter_3)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_4<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_Ord_cmp_6<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_cmp_Ordering_8> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_hash_Hash_hash_14<Self_, H>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<H> where Self_: 'static, H: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialOrd_partial_cmp_19<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_option_Option_12<core_cmp_Ordering_8>> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_hash_Hasher_finish_38<Self_>(p0: impl core::marker::Sized) -> Result<u64> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_hash_Hasher_write_39<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_54<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn builtin_auto_make_0() -> Result<builtin_auto_Inner_0> {
    let v0: *const () = (core_ptr_null_1::<u8>())?;
    Ok(builtin_auto_Inner_0 { ptr: v0 })
}

