
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

pub enum derive_CopyEnumOneVariant_0 {
    Variant(bool),
}

pub enum derive_ScalarEnum_1 {
    Variant0,
    Variant1,
    Variant2,
    Variant3,
}

pub enum derive_CopyEnum_2<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
}

pub enum derive_Enum_3<T> {
    Variant0,
    Variant1(bool),
    Variant2(u32),
    Variant3(T),
    Variant4(alloc_vec_Vec_9<T>),
}

pub enum derive_List_4<T> {
    Nil,
    Cons(T, Box<derive_List_4<T>>),
}

pub struct derive_CopyStruct_5<T> {
    pub f0: (),
    pub f1: bool,
    pub f2: u32,
    pub f3: T,
}

pub struct derive_Struct_6<T> {
    pub f: alloc_vec_Vec_9<T>,
}

pub struct derive_Struct6Fields_7 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub d: u32,
    pub e: u32,
    pub f: u32,
}

// TODO: opaque type alloc_vec_Vec_9 — emitting marker struct.
pub struct alloc_vec_Vec_9<T>(pub core::marker::PhantomData<fn() -> (T,)>);

pub struct alloc_alloc_Global_10;

// TODO: opaque type core_fmt_Formatter_13 — emitting marker struct.
pub struct core_fmt_Formatter_13;

pub enum core_result_Result_14<T, E> {
    Ok(T),
    Err(E),
}

pub struct core_fmt_Error_15;

pub fn core_clone_Clone_clone_4<Self_>(p0: impl core::marker::Sized) -> Result<Self_> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_7(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_eq_8<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_PartialEq_ne_9<Self_, Rhs>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where Self_: 'static, Rhs: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_15(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_21<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_27<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_33<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_38<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_44<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_derive_ne_50(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_ne_53<A, B>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where A: 'static, B: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_54<A, B>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where A: 'static, B: 'static {
    unimplemented!("opaque body")
}

pub fn core_cmp_Eq_assert_receiver_is_total_eq_55<Self_>(p0: impl core::marker::Sized) -> Result<()> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn core_fmt_Debug_fmt_56<Self_>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where Self_: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_debug_tuple_field1_finish_57(p0: impl core::marker::Sized, p1: impl core::marker::Sized, p2: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_write_str_59(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_60(p0: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn impl_core_clone_impls_clone_61(p0: impl core::marker::Sized) -> u32 {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_clone_63<T, A>(p0: impl core::marker::Sized) -> Result<alloc_vec_Vec_9<T>> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_boxed_clone_64<T, A>(p0: impl core::marker::Sized) -> Result<T> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_65(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_debug_struct_field4_finish_66(p0: impl core::marker::Sized, p1: impl core::marker::Sized, p2: impl core::marker::Sized, p3: impl core::marker::Sized, p4: impl core::marker::Sized, p5: impl core::marker::Sized, p6: impl core::marker::Sized, p7: impl core::marker::Sized, p8: impl core::marker::Sized, p9: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_partial_eq_eq_67<T, U, A1, A2>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static, U: 'static, A1: 'static, A2: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_debug_struct_field1_finish_68(p0: impl core::marker::Sized, p1: impl core::marker::Sized, p2: impl core::marker::Sized, p3: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_debug_struct_fields_finish_69(p0: impl core::marker::Sized, p1: impl core::marker::Sized, p2: impl core::marker::Sized, p3: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_70(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_ne_71(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_fmt_72<T>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_fmt_73(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_eq_77(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn impl_core_cmp_impls_ne_78(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> bool {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_num_fmt_79(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_alloc_alloc_clone_81(p0: impl core::marker::Sized) -> Result<alloc_alloc_Global_10> {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_partial_eq_ne_84<T, U, A1, A2>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static, U: 'static, A1: 'static, A2: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_vec_fmt_85<T, A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_boxed_eq_88<T, A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_alloc_boxed_ne_89<T, A>(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<bool> where T: 'static, A: 'static {
    unimplemented!("opaque body")
}

pub fn impl_core_fmt_fmt_91(p0: impl core::marker::Sized, p1: impl core::marker::Sized) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    unimplemented!("opaque body")
}

pub fn impl_derive_eq_26<T>(self_: derive_Enum_3<T>, other: derive_Enum_3<T>) -> Result<bool> where T: 'static {
    let self_0: isize = unimplemented!("placeholder");
    let other_1: isize = unimplemented!("placeholder");
    (if (self_0 == other_1) { match self_ {
    derive_Enum_3::Variant0 => Ok(true),
    derive_Enum_3::Variant1(__self_0_2) => match other {
    derive_Enum_3::Variant0 => Ok(true),
    derive_Enum_3::Variant1(__arg1_0_3) => (impl_core_cmp_impls_eq_70(__self_0_2, __arg1_0_3)),
    derive_Enum_3::Variant2(_) => Ok(true),
    derive_Enum_3::Variant3(_) => Ok(true),
    derive_Enum_3::Variant4(_) => Ok(true),
},
    derive_Enum_3::Variant2(__self_0_4) => match other {
    derive_Enum_3::Variant0 => Ok(true),
    derive_Enum_3::Variant1(_) => Ok(true),
    derive_Enum_3::Variant2(__arg1_0_5) => Ok((impl_core_cmp_impls_eq_77(__self_0_4, __arg1_0_5))),
    derive_Enum_3::Variant3(_) => Ok(true),
    derive_Enum_3::Variant4(_) => Ok(true),
},
    derive_Enum_3::Variant3(__self_0_6) => match other {
    derive_Enum_3::Variant0 => Ok(true),
    derive_Enum_3::Variant1(_) => Ok(true),
    derive_Enum_3::Variant2(_) => Ok(true),
    derive_Enum_3::Variant3(__arg1_0_7) => (impl_core_cmp_impls_eq_54::<T, T>(__self_0_6, __arg1_0_7)),
    derive_Enum_3::Variant4(_) => Ok(true),
},
    derive_Enum_3::Variant4(__self_0_8) => match other {
    derive_Enum_3::Variant0 => Ok(true),
    derive_Enum_3::Variant1(_) => Ok(true),
    derive_Enum_3::Variant2(_) => Ok(true),
    derive_Enum_3::Variant3(_) => Ok(true),
    derive_Enum_3::Variant4(__arg1_0_9) => (impl_alloc_vec_partial_eq_eq_67::<T, T, alloc_alloc_Global_10, alloc_alloc_Global_10>(__self_0_8, __arg1_0_9)),
},
} } else { Ok(false) })
}

pub fn impl_derive_eq_20<T>(self_: derive_CopyEnum_2<T>, other: derive_CopyEnum_2<T>) -> Result<bool> where T: 'static {
    let self_0: isize = unimplemented!("placeholder");
    let other_1: isize = unimplemented!("placeholder");
    (if (self_0 == other_1) { match self_ {
    derive_CopyEnum_2::Variant0 => Ok(true),
    derive_CopyEnum_2::Variant1(__self_0_2) => match other {
    derive_CopyEnum_2::Variant0 => Ok(true),
    derive_CopyEnum_2::Variant1(__arg1_0_3) => (impl_core_cmp_impls_eq_70(__self_0_2, __arg1_0_3)),
    derive_CopyEnum_2::Variant2(_) => Ok(true),
    derive_CopyEnum_2::Variant3(_) => Ok(true),
},
    derive_CopyEnum_2::Variant2(__self_0_4) => match other {
    derive_CopyEnum_2::Variant0 => Ok(true),
    derive_CopyEnum_2::Variant1(_) => Ok(true),
    derive_CopyEnum_2::Variant2(__arg1_0_5) => Ok((impl_core_cmp_impls_eq_77(__self_0_4, __arg1_0_5))),
    derive_CopyEnum_2::Variant3(_) => Ok(true),
},
    derive_CopyEnum_2::Variant3(__self_0_6) => match other {
    derive_CopyEnum_2::Variant0 => Ok(true),
    derive_CopyEnum_2::Variant1(_) => Ok(true),
    derive_CopyEnum_2::Variant2(_) => Ok(true),
    derive_CopyEnum_2::Variant3(__arg1_0_7) => (impl_core_cmp_impls_eq_54::<T, T>(__self_0_6, __arg1_0_7)),
},
} } else { Ok(false) })
}

pub fn impl_derive_eq_49(self_: derive_Struct6Fields_7, other: derive_Struct6Fields_7) -> Result<bool> {
    (if (self_.a == other.a) { (if (self_.b == other.b) { (if (self_.c == other.c) { (if (self_.d == other.d) { (if (self_.e == other.e) { Ok((self_.f == other.f)) } else { Ok(false) }) } else { Ok(false) }) } else { Ok(false) }) } else { Ok(false) }) } else { Ok(false) })
}

pub fn impl_derive_fmt_52(self_: derive_Struct6Fields_7, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    let v0: () = unimplemented!("placeholder");
    let v1: () = unimplemented!("placeholder");
    let v2: () = unimplemented!("placeholder");
    let v3: () = unimplemented!("placeholder");
    let v4: () = unimplemented!("placeholder");
    let v5: () = unimplemented!("placeholder");
    let values_6: Vec<()> = unimplemented!("placeholder");
    let v7: Vec<&'static str> = Ok(unimplemented!("FBuiltin call"))?;
    (impl_core_fmt_debug_struct_fields_finish_69(f, "Struct6Fields", v7, values_6))
}

pub fn impl_derive_fmt_29<T>(self_: derive_Enum_3<T>, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static {
    match self_ {
    derive_Enum_3::Variant0 => (impl_core_fmt_write_str_59(f, "Variant0")),
    derive_Enum_3::Variant1(__self_0_0) => {
    let __self_0_1: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant1", __self_0_1))
},
    derive_Enum_3::Variant2(__self_0_2) => {
    let __self_0_3: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant2", __self_0_3))
},
    derive_Enum_3::Variant3(__self_0_4) => {
    let __self_0_5: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant3", __self_0_5))
},
    derive_Enum_3::Variant4(__self_0_6) => {
    let __self_0_7: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant4", __self_0_7))
},
}
}

pub fn impl_derive_eq_32<T>(self_: derive_List_4<T>, other: derive_List_4<T>) -> Result<bool> where T: 'static {
    let self_0: isize = unimplemented!("placeholder");
    let other_1: isize = unimplemented!("placeholder");
    (if (self_0 == other_1) { match self_ {
    derive_List_4::Nil => Ok(true),
    derive_List_4::Cons(__self_0_2, __rec_3) => match other {
    derive_List_4::Nil => Ok(true),
    derive_List_4::Cons(__arg1_0_4, __rec_5) => {
    let v6: bool = (impl_core_cmp_impls_eq_54::<T, T>(__self_0_2, __arg1_0_4))?;
    (if v6 { (impl_derive_eq_32::<T>((*__rec_3), (*__rec_5))) } else { Ok(false) })
},
},
} } else { Ok(false) })
}

pub fn impl_derive_fmt_23<T>(self_: derive_CopyEnum_2<T>, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static {
    match self_ {
    derive_CopyEnum_2::Variant0 => (impl_core_fmt_write_str_59(f, "Variant0")),
    derive_CopyEnum_2::Variant1(__self_0_0) => {
    let __self_0_1: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant1", __self_0_1))
},
    derive_CopyEnum_2::Variant2(__self_0_2) => {
    let __self_0_3: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant2", __self_0_3))
},
    derive_CopyEnum_2::Variant3(__self_0_4) => {
    let __self_0_5: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant3", __self_0_5))
},
}
}

pub fn impl_derive_fmt_40<T>(self_: derive_CopyStruct_5<T>, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static {
    let v0: () = unimplemented!("placeholder");
    let v1: () = unimplemented!("placeholder");
    let v2: () = unimplemented!("placeholder");
    let v3: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_struct_field4_finish_66(f, "CopyStruct", "f0", v0, "f1", v1, "f2", v2, "f3", v3))
}

pub fn impl_derive_eq_37<T>(self_: derive_CopyStruct_5<T>, other: derive_CopyStruct_5<T>) -> Result<bool> where T: 'static {
    let v0: bool = (impl_core_cmp_impls_eq_65((), ()))?;
    (if v0 { (if (self_.f1 == other.f1) { (if (self_.f2 == other.f2) { unimplemented!("TraitMethod") } else { Ok(false) }) } else { Ok(false) }) } else { Ok(false) })
}

pub fn impl_derive_clone_24<T>(self_: derive_Enum_3<T>) -> Result<derive_Enum_3<T>> where T: 'static {
    match self_ {
    derive_Enum_3::Variant0 => Ok(derive_Enum_3::<T>::Variant0),
    derive_Enum_3::Variant1(__self_0_0) => {
    let v1: bool = Ok((impl_core_clone_impls_clone_60(__self_0_0)))?;
    Ok(derive_Enum_3::Variant1(v1))
},
    derive_Enum_3::Variant2(__self_0_2) => {
    let v3: u32 = Ok((impl_core_clone_impls_clone_61(__self_0_2)))?;
    Ok(derive_Enum_3::Variant2(v3))
},
    derive_Enum_3::Variant3(__self_0_4) => {
    let v5: T = (Err::<T, ()>(()))?;
    Ok(derive_Enum_3::Variant3(v5))
},
    derive_Enum_3::Variant4(__self_0_6) => {
    let v7: alloc_vec_Vec_9<T> = (impl_alloc_vec_clone_63::<T, alloc_alloc_Global_10>(__self_0_6))?;
    Ok(derive_Enum_3::Variant4(v7))
},
}
}

pub fn impl_derive_clone_47(self_: derive_Struct6Fields_7) -> Result<derive_Struct6Fields_7> {
    let v0: u32 = Ok((impl_core_clone_impls_clone_61(self_.a)))?;
    let v1: u32 = Ok((impl_core_clone_impls_clone_61(self_.b)))?;
    let v2: u32 = Ok((impl_core_clone_impls_clone_61(self_.c)))?;
    let v3: u32 = Ok((impl_core_clone_impls_clone_61(self_.d)))?;
    let v4: u32 = Ok((impl_core_clone_impls_clone_61(self_.e)))?;
    let v5: u32 = Ok((impl_core_clone_impls_clone_61(self_.f)))?;
    Ok(derive_Struct6Fields_7 { a: v0, b: v1, c: v2, d: v3, e: v4, f: v5 })
}

pub fn impl_derive_clone_18<T>(self_: derive_CopyEnum_2<T>) -> Result<derive_CopyEnum_2<T>> where T: 'static {
    match self_ {
    derive_CopyEnum_2::Variant0 => Ok(derive_CopyEnum_2::<T>::Variant0),
    derive_CopyEnum_2::Variant1(__self_0_0) => {
    let v1: bool = Ok((impl_core_clone_impls_clone_60(__self_0_0)))?;
    Ok(derive_CopyEnum_2::Variant1(v1))
},
    derive_CopyEnum_2::Variant2(__self_0_2) => {
    let v3: u32 = Ok((impl_core_clone_impls_clone_61(__self_0_2)))?;
    Ok(derive_CopyEnum_2::Variant2(v3))
},
    derive_CopyEnum_2::Variant3(__self_0_4) => {
    let v5: T = (Err::<T, ()>(()))?;
    Ok(derive_CopyEnum_2::Variant3(v5))
},
}
}

pub fn impl_derive_fmt_17(self_: derive_ScalarEnum_1, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    match self_ {
    derive_ScalarEnum_1::Variant0 => (impl_core_fmt_write_str_59(f, "Variant0")),
    derive_ScalarEnum_1::Variant1 => (impl_core_fmt_write_str_59(f, "Variant1")),
    derive_ScalarEnum_1::Variant2 => (impl_core_fmt_write_str_59(f, "Variant2")),
    derive_ScalarEnum_1::Variant3 => (impl_core_fmt_write_str_59(f, "Variant3")),
}
}

pub fn impl_derive_clone_35<T>(self_: derive_CopyStruct_5<T>) -> Result<derive_CopyStruct_5<T>> where T: 'static {
    let _: () = (Err::<(), ()>(()))?;
    let v0: bool = Ok((impl_core_clone_impls_clone_60(self_.f1)))?;
    let v1: u32 = Ok((impl_core_clone_impls_clone_61(self_.f2)))?;
    let v2: T = (Err::<T, ()>(()))?;
    Ok(derive_CopyStruct_5 { f0: (), f1: v0, f2: v1, f3: v2 })
}

pub fn impl_derive_fmt_46<T>(self_: derive_Struct_6<T>, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> where T: 'static {
    let v0: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_struct_field1_finish_68(f, "Struct", "f", v0))
}

pub fn impl_derive_clone_30<T>(self_: derive_List_4<T>) -> Result<derive_List_4<T>> where T: 'static {
    match self_ {
    derive_List_4::Nil => Ok(derive_List_4::<T>::Nil),
    derive_List_4::Cons(__self_0_0, __rec_1) => {
    let v2: T = (Err::<T, ()>(()))?;
    let v3: derive_List_4<T> = (impl_derive_clone_30::<T>((*__rec_1)))?;
    Ok(derive_List_4::Cons(v2, Box::new(v3)))
},
}
}

pub fn impl_derive_fmt_11(self_: derive_CopyEnumOneVariant_0, f: core_fmt_Formatter_13) -> Result<(core_result_Result_14<(), core_fmt_Error_15>, core_fmt_Formatter_13)> {
    let adt_0: derive_CopyEnumOneVariant_0 = self_;
    let __self_0_1: () = unimplemented!("placeholder");
    (impl_core_fmt_debug_tuple_field1_finish_57(f, "Variant", __self_0_1))
}

pub fn impl_derive_eq_6(self_: derive_CopyEnumOneVariant_0, other: derive_CopyEnumOneVariant_0) -> Result<bool> {
    let adt_0: derive_CopyEnumOneVariant_0 = self_;
    let adt_1: derive_CopyEnumOneVariant_0 = other;
    (impl_core_cmp_impls_eq_70(adt_0, adt_1))
}

pub fn impl_derive_eq_14(self_: derive_ScalarEnum_1, other: derive_ScalarEnum_1) -> Result<bool> {
    let self_0: isize = unimplemented!("placeholder");
    let other_1: isize = unimplemented!("placeholder");
    Ok((self_0 == other_1))
}

pub fn impl_derive_clone_41<T>(self_: derive_Struct_6<T>) -> Result<derive_Struct_6<T>> where T: 'static {
    let v0: alloc_vec_Vec_9<T> = (impl_alloc_vec_clone_63::<T, alloc_alloc_Global_10>(self_.f))?;
    Ok(derive_Struct_6 { f: v0 })
}

pub fn derive_refs_ne_0(a: derive_Struct6Fields_7, b: derive_Struct6Fields_7) -> Result<bool> {
    (impl_core_cmp_impls_ne_53::<derive_Struct6Fields_7, derive_Struct6Fields_7>(a, b))
}

pub fn derive_refs_eq_1(a: derive_Struct6Fields_7, b: derive_Struct6Fields_7) -> Result<bool> {
    (impl_derive_eq_49(a, b))
}

pub fn impl_derive_eq_43<T>(self_: derive_Struct_6<T>, other: derive_Struct_6<T>) -> Result<bool> where T: 'static {
    (impl_alloc_vec_partial_eq_eq_67::<T, T, alloc_alloc_Global_10, alloc_alloc_Global_10>(self_.f, other.f))
}

pub fn impl_derive_assert_receiver_is_total_eq_10(self_: derive_CopyEnumOneVariant_0) -> Result<()> {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_16(self_: derive_ScalarEnum_1) -> Result<()> {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_22<T>(self_: derive_CopyEnum_2<T>) -> Result<()> where T: 'static {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_28<T>(self_: derive_Enum_3<T>) -> Result<()> where T: 'static {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_34<T>(self_: derive_List_4<T>) -> Result<()> where T: 'static {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_39<T>(self_: derive_CopyStruct_5<T>) -> Result<()> where T: 'static {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_45<T>(self_: derive_Struct_6<T>) -> Result<()> where T: 'static {
    Ok(())
}

pub fn impl_derive_assert_receiver_is_total_eq_51(self_: derive_Struct6Fields_7) -> Result<()> {
    Ok(())
}

pub fn impl_derive_clone_2(self_: derive_CopyEnumOneVariant_0) -> Result<derive_CopyEnumOneVariant_0> {
    Ok(self_)
}

pub fn impl_derive_clone_12(self_: derive_ScalarEnum_1) -> Result<derive_ScalarEnum_1> {
    Ok(self_)
}

