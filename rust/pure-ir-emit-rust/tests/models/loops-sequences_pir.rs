
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

pub struct loops_sequences_Key_0 {
    pub seed: [u8; 32usize],
    pub t: [u16; 32usize],
}

pub fn loops_sequences_key_expand_5(key: loops_sequences_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize]) -> Result<(loops_sequences_Key_0, [u8; 8usize], [u8; 8usize])> {
    let state_base_0: [u8; 8usize] = (loops_sequences_shake_init_0(state_base))?;
    let v1: Vec<u8> = Ok(unimplemented!("FBuiltin call"))?;
    let state_base_2: [u8; 8usize] = (loops_sequences_shake_append_1(state_base_0, v1))?;
    let (key_3, state_work_4, sample_buffer_5): (loops_sequences_Key_0, [u8; 8usize], [u8; 1usize]) = (loops_sequences_key_expand_5_loop0(key, state_base_2, state_work, [0u8], 0i32))?;
    let (key_6, state_work_7): (loops_sequences_Key_0, [u8; 8usize]) = (loops_sequences_key_expand_5_loop1(key_3, state_base_2, state_work_4, sample_buffer_5, 0i32))?;
    Ok((key_6, state_base_2, state_work_7))
}

pub fn impl_loops_sequences_t_mut_6(self_: loops_sequences_Key_0) -> Result<([u16; 32usize], Box<dyn FnOnce([u16; 32usize]) -> loops_sequences_Key_0>)> {
    let back_0: Box<dyn FnOnce([u16; 32usize]) -> loops_sequences_Key_0> = (Box::new(move |v1: [u16; 32usize]| -> loops_sequences_Key_0 { loops_sequences_Key_0 { seed: self_.seed, t: v1 } }) as Box<dyn FnOnce([u16; 32usize]) -> loops_sequences_Key_0>);
    Ok((self_.t, back_0))
}

pub fn loops_sequences_shake_init_0(_state: [u8; 8usize]) -> Result<[u8; 8usize]> {
    Ok(_state)
}

pub fn loops_sequences_shake_append_1(_state: [u8; 8usize], _data: Vec<u8>) -> Result<[u8; 8usize]> {
    Ok(_state)
}

pub fn loops_sequences_shake_state_copy_2(_src: [u8; 8usize], _dst: [u8; 8usize]) -> Result<[u8; 8usize]> {
    Ok(_dst)
}

pub fn loops_sequences_shake_extract_3(_src: [u8; 8usize], _dst: Vec<u8>) -> Result<Vec<u8>> {
    Ok(_dst)
}

pub fn loops_sequences_sample_cbd_4(_src: Vec<u8>, _dst: [u16; 32usize]) -> Result<[u16; 32usize]> {
    Ok(_dst)
}

pub fn loops_sequences_key_expand_5_loop0(key: loops_sequences_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize], sample_buffer: [u8; 1usize], i: i32) -> Result<(loops_sequences_Key_0, [u8; 8usize], [u8; 1usize])> {
    panic!("LoopOp placeholder")
}

pub fn loops_sequences_key_expand_5_loop1(key: loops_sequences_Key_0, state_base: [u8; 8usize], state_work: [u8; 8usize], sample_buffer: [u8; 1usize], i: i32) -> Result<(loops_sequences_Key_0, [u8; 8usize])> {
    panic!("LoopOp placeholder")
}

