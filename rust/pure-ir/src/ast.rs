//! Hand-written AST mirroring the Phase-1 subset of `Pure.ml`.
//!
//! Encoding convention (matches `src/pure/PureJson.ml`): every tagged
//! sum serializes as `{"kind": "VariantName", "payload": <data>}`.
//! Serde's `tag = "kind", content = "payload"` adapter handles this
//! directly. Variants the OCaml side has not implemented yet share
//! the kind `"UNSUPPORTED"` with a string payload naming the missing
//! constructor.

use serde::Deserialize;

// ---------- Literals & literal types ----------

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(tag = "kind", content = "payload")]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub enum UIntTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum LiteralType {
    TInt(IntTy),
    TUInt(UIntTy),
    TFloat(FloatTy),
    TBool,
    TChar,
    TPureNat,
    TPureInt,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ScalarValue {
    pub signed: bool,
    /// Either an [`IntTy`] (`signed: true`) or a [`UIntTy`]
    /// (`signed: false`); kept as raw JSON for Phase 1.
    pub ty: serde_json::Value,
    /// Z (arbitrary-precision) integer rendered as a decimal string.
    pub value: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FloatValue {
    pub value: String,
    pub ty: FloatTy,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Literal {
    VScalar(ScalarValue),
    VFloat(FloatValue),
    VBool(bool),
    VChar(u32),
    VByteStr(Vec<u32>),
    VStr(String),
    VPureNat(String),
    VPureInt(String),
}

// ---------- Types ----------

/// `TLiteral` / `TArrow` cover the Phase-1 subset; everything else
/// flows through [`Ty::Unsupported`] with the OCaml constructor name.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Ty {
    TLiteral(LiteralType),
    TArrow(TArrow),
    #[serde(rename = "UNSUPPORTED")]
    Unsupported(String),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TArrow {
    pub input: Box<Ty>,
    pub output: Box<Ty>,
}

// ---------- Expressions ----------

#[derive(Debug, Clone, Deserialize)]
pub struct BVar {
    pub scope: i64,
    pub id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct App {
    #[serde(rename = "fun")]
    pub fun_: Box<TExpr>,
    pub arg: Box<TExpr>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Expr {
    FVar(u64),
    BVar(BVar),
    Const(Literal),
    App(App),
    #[serde(rename = "UNSUPPORTED")]
    Unsupported(String),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TExpr {
    pub e: Expr,
    pub ty: Ty,
}

// ---------- Signatures, bodies, declarations ----------

#[derive(Debug, Clone, Deserialize)]
pub struct FunSig {
    pub inputs: Vec<Ty>,
    pub output: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunBody {
    /// Phase 1 does not model `tpat` yet — we only carry the arity.
    pub num_inputs: u32,
    pub body: TExpr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunDecl {
    pub def_id: u64,
    pub name: String,
    pub signature: FunSig,
    pub is_global_decl_body: bool,
    pub num_loops: u32,
    pub body: Option<FunBody>,
}

/// Phase-1 stubs for the other top-level decls. They carry just
/// enough to round-trip the envelope; richer modeling lands in Phase 2.
#[derive(Debug, Clone, Deserialize)]
pub struct TypeDeclStub {
    pub def_id: u64,
    #[serde(default)]
    pub _unsupported: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GlobalDeclStub {
    pub def_id: u64,
    pub name: String,
    #[serde(default)]
    pub _unsupported: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDeclStub {
    pub name: String,
    #[serde(default)]
    pub _unsupported: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitImplStub {
    pub name: String,
    #[serde(default)]
    pub _unsupported: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TranslatedCrate {
    pub pure_ir_fmt_version: u32,
    pub stage: String,
    pub crate_name: String,
    pub type_decls: Vec<TypeDeclStub>,
    pub fun_decls: Vec<FunDecl>,
    pub global_decls: Vec<GlobalDeclStub>,
    pub trait_decls: Vec<TraitDeclStub>,
    pub trait_impls: Vec<TraitImplStub>,
}
