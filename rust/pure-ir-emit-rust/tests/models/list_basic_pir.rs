
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

pub enum list_basic_List_0 {
    Cons(u32, Box<list_basic_List_0>),
    Nil,
}

pub struct alloc_alloc_Global_1;

pub fn impl_core_num_wrapping_add_2(p0: u32, p1: u32) -> u32 {
    // route: core_models::num::*::wrapping_add → rust_primitives::arithmetic::wrapping_add_<t>
    u32::wrapping_add(p0, p1)
}

pub fn list_basic_list_len_0(xs: list_basic_List_0) -> Result<u32> {
    match xs {
    list_basic_List_0::Cons(_, __rec_0) => {
    let v1: u32 = (list_basic_list_len_0((*__rec_0)))?;
    Ok((impl_core_num_wrapping_add_2(v1, 1u32)))
},
    list_basic_List_0::Nil => Ok(0u32),
}
}

