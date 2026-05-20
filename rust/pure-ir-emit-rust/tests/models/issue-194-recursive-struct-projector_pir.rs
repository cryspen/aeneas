
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

pub struct issue_194_recursive_struct_projector_AVLNode_0<T> {
    pub value: T,
    pub left: Box<core_option_Option_2<issue_194_recursive_struct_projector_AVLNode_0<T>>>,
    pub right: Box<core_option_Option_2<issue_194_recursive_struct_projector_AVLNode_0<T>>>,
}

pub enum core_option_Option_2<T> {
    None,
    Some(T),
}

pub fn issue_194_recursive_struct_projector_get_val_0<T>(x: issue_194_recursive_struct_projector_AVLNode_0<T>) -> Result<T> where T: 'static {
    Ok(x.value)
}

pub fn issue_194_recursive_struct_projector_get_left_1<T>(x: issue_194_recursive_struct_projector_AVLNode_0<T>) -> Result<core_option_Option_2<issue_194_recursive_struct_projector_AVLNode_0<T>>> where T: 'static {
    Ok((*x.left))
}

