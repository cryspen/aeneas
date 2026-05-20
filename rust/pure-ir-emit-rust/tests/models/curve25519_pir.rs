
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

pub struct curve25519_Scalar52_0([u64; 5usize]);

pub fn core_ops_index_Index_index_3<Self_, Idx, Clause0_Output>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<Clause0_Output> where Self_: 'static, Idx: 'static, Clause0_Output: 'static {
    unimplemented!("opaque body")
}

pub fn curve25519_mul_internal_1(a: curve25519_Scalar52_0, b: curve25519_Scalar52_0) -> Result<[u128; 9usize]> {
    let z_0: [u128; 9usize] = unimplemented!("placeholder");
    let v1: u64 = (impl_curve25519_index_2(a, 0usize))?;
    let v2: u64 = (impl_curve25519_index_2(b, 0usize))?;
    let v3: u128 = (curve25519_m_0(v1, v2))?;
    let z_4: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v5: u64 = (impl_curve25519_index_2(b, 1usize))?;
    let v6: u128 = (curve25519_m_0(v1, v5))?;
    let v7: u64 = (impl_curve25519_index_2(a, 1usize))?;
    let v8: u128 = (curve25519_m_0(v7, v2))?;
    let v9: u128 = (v6.checked_add(v8).ok_or(()))?;
    let z_10: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v11: u64 = (impl_curve25519_index_2(b, 2usize))?;
    let v12: u128 = (curve25519_m_0(v1, v11))?;
    let v13: u128 = (curve25519_m_0(v7, v5))?;
    let v14: u128 = (v12.checked_add(v13).ok_or(()))?;
    let v15: u64 = (impl_curve25519_index_2(a, 2usize))?;
    let v16: u128 = (curve25519_m_0(v15, v2))?;
    let v17: u128 = (v14.checked_add(v16).ok_or(()))?;
    let z_18: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v19: u64 = (impl_curve25519_index_2(b, 3usize))?;
    let v20: u128 = (curve25519_m_0(v1, v19))?;
    let v21: u128 = (curve25519_m_0(v7, v11))?;
    let v22: u128 = (v20.checked_add(v21).ok_or(()))?;
    let v23: u128 = (curve25519_m_0(v15, v5))?;
    let v24: u128 = (v22.checked_add(v23).ok_or(()))?;
    let v25: u64 = (impl_curve25519_index_2(a, 3usize))?;
    let v26: u128 = (curve25519_m_0(v25, v2))?;
    let v27: u128 = (v24.checked_add(v26).ok_or(()))?;
    let z_28: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v29: u64 = (impl_curve25519_index_2(b, 4usize))?;
    let v30: u128 = (curve25519_m_0(v1, v29))?;
    let v31: u128 = (curve25519_m_0(v7, v19))?;
    let v32: u128 = (v30.checked_add(v31).ok_or(()))?;
    let v33: u128 = (curve25519_m_0(v15, v11))?;
    let v34: u128 = (v32.checked_add(v33).ok_or(()))?;
    let v35: u128 = (curve25519_m_0(v25, v5))?;
    let v36: u128 = (v34.checked_add(v35).ok_or(()))?;
    let v37: u64 = (impl_curve25519_index_2(a, 4usize))?;
    let v38: u128 = (curve25519_m_0(v37, v2))?;
    let v39: u128 = (v36.checked_add(v38).ok_or(()))?;
    let z_40: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v41: u128 = (curve25519_m_0(v7, v29))?;
    let v42: u128 = (curve25519_m_0(v15, v19))?;
    let v43: u128 = (v41.checked_add(v42).ok_or(()))?;
    let v44: u128 = (curve25519_m_0(v25, v11))?;
    let v45: u128 = (v43.checked_add(v44).ok_or(()))?;
    let v46: u128 = (curve25519_m_0(v37, v5))?;
    let v47: u128 = (v45.checked_add(v46).ok_or(()))?;
    let z_48: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v49: u128 = (curve25519_m_0(v15, v29))?;
    let v50: u128 = (curve25519_m_0(v25, v19))?;
    let v51: u128 = (v49.checked_add(v50).ok_or(()))?;
    let v52: u128 = (curve25519_m_0(v37, v11))?;
    let v53: u128 = (v51.checked_add(v52).ok_or(()))?;
    let z_54: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v55: u128 = (curve25519_m_0(v25, v29))?;
    let v56: u128 = (curve25519_m_0(v37, v19))?;
    let v57: u128 = (v55.checked_add(v56).ok_or(()))?;
    let z_58: [u128; 9usize] = (Err::<[u128; 9usize], ()>(()))?;
    let v59: u128 = (curve25519_m_0(v37, v29))?;
    Err::<_, ()>(())
}

pub fn curve25519_m_0(x: u64, y: u64) -> Result<u128> {
    let v0: u128 = Ok((x as u128))?;
    let v1: u128 = Ok((y as u128))?;
    (v0.checked_mul(v1).ok_or(()))
}

pub fn impl_curve25519_index_2(self_: curve25519_Scalar52_0, _index: usize) -> Result<u64> {
    unimplemented!("FBuiltin call")
}

