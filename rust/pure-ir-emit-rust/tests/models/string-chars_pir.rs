
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

// TODO: opaque type alloc_vec_Vec_0 — emitting marker struct.
pub struct alloc_vec_Vec_0<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_1;

// TODO: opaque type core_str_iter_Chars_2 — emitting marker struct.
pub struct core_str_iter_Chars_2;

// TODO: opaque type core_fmt_Arguments_3 — emitting marker struct.
pub struct core_fmt_Arguments_3;

// TODO: opaque type core_fmt_rt_Argument_4 — emitting marker struct.
pub struct core_fmt_rt_Argument_4;

pub enum core_option_Option_6<T> {
    None,
    Some(T),
}

pub enum core_result_Result_7<T, E> {
    Ok(T),
    Err(E),
}

// TODO: opaque type core_fmt_Formatter_38 — emitting marker struct.
pub struct core_fmt_Formatter_38;

pub struct core_fmt_Error_39;

pub fn impl_core_str_chars_2(p0: impl core::marker::Sized) -> Result<core_str_iter_Chars_2> {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_collect_3<Self_, B, Clause0_Item>(p0: impl core::marker::Sized) -> Result<B> where Self_: 'static, B: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_slice_to_vec_5<T>(p0: impl core::marker::Sized) -> Result<alloc_vec_Vec_0<T>> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_rt_new_debug_6<T>(p0: impl core::marker::Sized) -> Result<core_fmt_rt_Argument_4> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_new_7<const N: usize, const M: usize>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<core_fmt_Arguments_3> {
    unimplemented!("opaque body")
}

pub fn std_io_stdio__print_8(p0: impl core::marker::Sized) -> Result<()> {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_collect_FromIterator_from_iter_9<Self_, A, T, Clause1_IntoIter>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static, A: 'static, T: 'static, Clause1_IntoIter: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_from_iter_10<T, I, Clause0_IntoIter>(p0: impl core::marker::Sized) -> Result<alloc_vec_Vec_0<T>> where T: 'static, I: 'static, Clause0_IntoIter: 'static {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_iterator_Iterator_next_11<Self_, Clause0_Item>(p0: impl core::marker::Sized) -> Result<(core_option_Option_6<Clause0_Item>, Self_)> where Self_: 'static, Clause0_Item: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_str_iter_collect_117<B>(p0: impl core::marker::Sized) -> Result<B> where B: 'static {
    unimplemented!("opaque body")
}

pub fn core_clone_Clone_clone_166<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_168(p0: impl core::marker::Sized) -> i32 {
    unimplemented!("opaque body")
}

pub fn core_fmt_Debug_fmt_170<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_7<(), core_fmt_Error_39>, core_fmt_Formatter_38)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_fmt_171<T, A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_7<(), core_fmt_Error_39>, core_fmt_Formatter_38)> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_num_fmt_172(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_7<(), core_fmt_Error_39>, core_fmt_Formatter_38)> {
    unimplemented!("opaque body")
}

pub fn core_iter_traits_collect_IntoIterator_into_iter_173<Self_, Clause0_Item, Clause0_IntoIter>(p0: impl core::marker::Sized) -> Result<Clause0_IntoIter> where Self_: 'static, Clause0_Item: 'static, Clause0_IntoIter: 'static {
    unimplemented!("opaque body")
}

pub fn string_chars_print_vec_1() -> Result<()> {
    let v0: Vec<i32> = Ok(unimplemented!("FBuiltin call"))?;
    let v_1: alloc_vec_Vec_0<i32> = (impl_alloc_slice_to_vec_5::<i32>(v0))?;
    let v2: core_fmt_rt_Argument_4 = (impl_core_fmt_rt_new_debug_6::<alloc_vec_Vec_0<i32>>(v_1))?;
    let v3: core_fmt_Arguments_3 = (impl_core_fmt_new_7::<4usize, 1usize>([192u8, 1u8, 10u8, 0u8], v2))?;
    (std_io_stdio__print_8(v3))
}

pub fn string_chars_collect_0() -> Result<()> {
    let v0: core_str_iter_Chars_2 = (impl_core_str_chars_2("hello"))?;
    let _: alloc_vec_Vec_0<char> = (impl_core_str_iter_collect_117::<alloc_vec_Vec_0<char>>(v0))?;
    Ok(())
}

