//! Hand-written AST mirroring `src/pure/PureJson.ml`.
//!
//! Encoding convention (matches the OCaml emit): every tagged sum
//! serializes as `{"kind": "VariantName", "payload": <data>}`. Serde's
//! `tag = "kind", content = "payload"` adapter handles this directly.
//! Records become structs with matching `snake_case` field names.
//! Identifiers (anything from an `IdGen()` module on the OCaml side)
//! arrive as JSON ints; we model them as `u64`.
//!
//! Starting at `pure_ir_fmt_version = 2`, source spans + Charon
//! `attr_info` ride along on every decl, loop, and `Meta` expression
//! node (see the `Span`, `AttrInfo`, `ItemMeta`, and `EMeta` types
//! below). The `Span` shape matches `CertJson.json_cert_source_span`
//! verbatim so future consumers can share a parser.

use serde::Deserialize;

// ---------- Source spans + Charon attribute / item meta ----------

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct Span {
    pub file: String,
    pub beg_line: u32,
    pub beg_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum InlineAttr {
    Hint,
    Never,
    Always,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct RawAttribute {
    pub path: String,
    pub args: Option<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "payload")]
pub enum Attribute {
    AttrOpaque,
    AttrExclude,
    AttrRename(String),
    AttrVariantsPrefix(String),
    AttrVariantsSuffix(String),
    AttrDocComment(String),
    AttrUnknown(RawAttribute),
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct AttrInfo {
    pub attributes: Vec<Attribute>,
    pub inline: Option<InlineAttr>,
    pub rename: Option<String>,
    pub public: bool,
}

/// Charon `path_elem`. The heavy `PeImpl` / `PeInstantiated` variants
/// are opaque on the wire — they're carried as a tag with `null`
/// payload to keep the schema bounded; `PeIdent` and `PeTarget` ship
/// their full payloads.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "payload")]
pub enum PathElem {
    PeIdent(PeIdentPayload),
    PeImpl,
    PeInstantiated,
    PeTarget(String),
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct PeIdentPayload {
    pub name: String,
    pub disambiguator: u64,
}

pub type CharonName = Vec<PathElem>;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum ItemOpacity {
    Transparent,
    Foreign,
    ItemOpaque,
    Invisible,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ItemMeta {
    pub name: CharonName,
    pub span: Span,
    pub source_text: Option<String>,
    pub attr_info: AttrInfo,
    pub is_local: bool,
    pub opacity: ItemOpacity,
    pub lang_item: Option<String>,
}

// ---------- Literals & atomic types ----------

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum UIntTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "payload")]
pub enum IntegerType {
    Signed(IntTy),
    Unsigned(UIntTy),
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum OverflowMode {
    OPanic,
    OUB,
    OWrap,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum Mutability {
    Mut,
    Const,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub enum ArrayOrSlice {
    Array,
    Slice,
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
    /// (`signed: false`); kept as raw JSON to avoid an untagged enum.
    pub ty: serde_json::Value,
    /// Arbitrary-precision integer rendered as a decimal string.
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

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum BuiltinTy {
    TResult,
    TSum,
    TLoopResult,
    TError,
    TFuel,
    TArray,
    TSlice,
    TStr,
    TRawPtr(Mutability),
}

// ---------- De-Bruijn variables ----------

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum DeBruijnVar<T> {
    Bound(DeBruijnBound<T>),
    Free(T),
}

#[derive(Debug, Clone, Deserialize)]
pub struct DeBruijnBound<T> {
    pub db: u32,
    pub value: T,
}

// ---------- Types ----------

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Ty {
    TLiteral(LiteralType),
    TArrow(TArrow),
    TAdt(TAdt),
    TVar(DeBruijnVar<u64>),
    TTraitType(TTraitType),
    TNever,
    TDynTrait(DynPredicate),
    TError,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TArrow {
    pub input: Box<Ty>,
    pub output: Box<Ty>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TAdt {
    pub type_id: TypeId,
    pub generics: GenericArgs,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TTraitType {
    pub trait_ref: TraitRef,
    pub assoc_type_id: u64,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum TypeId {
    TAdtId(u64),
    TTuple,
    TBuiltin(BuiltinTy),
}

#[derive(Debug, Clone, Deserialize)]
pub struct GenericArgs {
    pub types: Vec<Ty>,
    pub const_generics: Vec<ConstGeneric>,
    pub trait_refs: Vec<TraitRef>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum ConstGeneric {
    CgGlobal(u64),
    CgVar(DeBruijnVar<u64>),
    CgValue(Literal),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitRef {
    pub trait_id: TraitInstanceId,
    pub trait_decl_ref: TraitDeclRef,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDeclRef {
    pub trait_decl_id: u64,
    pub decl_generics: GenericArgs,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunDeclRef {
    pub fun_id: u64,
    pub fun_generics: GenericArgs,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GlobalDeclRef {
    pub global_id: u64,
    pub global_generics: GenericArgs,
}

/// `Self` on the OCaml side is a reserved word in Rust, so the variant
/// is renamed `SelfTy`. The JSON tag stays `"Self"`.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum TraitInstanceId {
    #[serde(rename = "Self")]
    SelfTy,
    TraitImpl(TraitImplInstance),
    Clause(DeBruijnVar<u64>),
    ParentClause(ParentClause),
    BuiltinOrAuto(BuiltinImplData),
    UnknownTrait(String),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitImplInstance {
    pub impl_id: u64,
    pub generics: GenericArgs,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ParentClause {
    pub parent: Box<TraitInstanceId>,
    pub trait_decl_id: u64,
    pub clause_id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub enum BuiltinImplData {
    BuiltinCopy,
    BuiltinClone,
    BuiltinDiscriminantKind,
    BuiltinFn,
    BuiltinFnMut,
    BuiltinFnOnce,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DynPredicate {
    pub params: GenericParams,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GenericParams {
    pub types: Vec<TypeParam>,
    pub const_generics: Vec<ConstGenericParam>,
    pub trait_clauses: Vec<TraitParam>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TypeParam {
    pub index: u64,
    pub name: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ConstGenericParam {
    pub index: u64,
    pub name: String,
    pub ty: LiteralType,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitParam {
    pub clause_id: u64,
    pub trait_id: u64,
    pub generics: GenericArgs,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitTypeConstraint {
    pub trait_ref: TraitRef,
    pub type_id: u64,
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Predicates {
    pub trait_type_constraints: Vec<TraitTypeConstraint>,
}

// ---------- Operators ----------

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Binop {
    BitXor(BinopIntTy),
    BitAnd(BinopIntTy),
    BitOr(BinopIntTy),
    Eq(BinopTy),
    Ne(BinopTy),
    Lt(BinopIntTy),
    Le(BinopIntTy),
    Ge(BinopIntTy),
    Gt(BinopIntTy),
    Add(BinopChecked),
    Sub(BinopChecked),
    Mul(BinopChecked),
    Div(BinopChecked),
    Rem(BinopChecked),
    AddChecked(BinopIntTy),
    SubChecked(BinopIntTy),
    MulChecked(BinopIntTy),
    Shl(BinopShift),
    Shr(BinopShift),
    Cmp(BinopIntTy),
    BoolOr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BinopIntTy {
    pub ty: IntegerType,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BinopTy {
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BinopChecked {
    pub overflow_mode: OverflowMode,
    pub ty: IntegerType,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BinopShift {
    pub overflow_mode: OverflowMode,
    pub lhs_ty: IntegerType,
    pub rhs_ty: IntegerType,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum CastKind {
    CastLit(CastLit),
    CastRawPtr(CastRawPtr),
}

#[derive(Debug, Clone, Deserialize)]
pub struct CastLit {
    pub src: LiteralType,
    pub dst: LiteralType,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CastRawPtr {
    pub src: CastRawPtrSide,
    pub dst: CastRawPtrSide,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CastRawPtrSide {
    pub ty: LiteralType,
    pub mutability: Mutability,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Unop {
    Not(Option<IntegerType>),
    Neg(IntegerType),
    Cast(CastKind),
    ArrayToSlice,
}

// ---------- Qualifiers ----------

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum PureBuiltinFunId {
    Return,
    Fail,
    Assert,
    Loop(u32),
    RecLoopCall(u32),
    FuelDecrease,
    FuelEqZero,
    UpdateAtIndex(ArrayOrSlice),
    ToResult,
    Discriminant,
    ResultUnwrapMut,
    GetTarget,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum LlbcFunId {
    FRegular(u64),
    FBuiltin,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum FnPtrKind {
    FunId(LlbcFunId),
    TraitMethod(TraitMethodCall),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitMethodCall {
    pub trait_ref: TraitRef,
    pub method_id: u64,
    pub fun_decl_id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct RegularFunId {
    pub kind: FnPtrKind,
    #[serde(rename = "loop")]
    pub loop_: Option<LoopMarker>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LoopMarker {
    pub loop_id: u64,
    pub is_body: bool,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum FunId {
    FromLlbc(RegularFunId),
    Pure(PureBuiltinFunId),
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum FunOrOpId {
    Fun(FunId),
    Unop(Unop),
    Binop(Binop),
}

#[derive(Debug, Clone, Deserialize)]
pub struct AdtConsId {
    pub adt_id: TypeId,
    pub variant_id: Option<u64>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Projection {
    pub adt_id: TypeId,
    pub field_id: u64,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum QualifId {
    FunOrOp(FunOrOpId),
    Global(u64),
    AdtCons(AdtConsId),
    Proj(Projection),
    ScalarValProj(IntegerType),
    TraitConst(TraitConst),
    MkDynTrait(TraitRef),
    LoopOp,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitConst {
    pub trait_ref: TraitRef,
    pub assoc_const_id: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Qualif {
    pub id: QualifId,
    pub generics: GenericArgs,
}

// ---------- Patterns ----------

#[derive(Debug, Clone, Deserialize)]
pub struct Var {
    pub basename: Option<String>,
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FVar {
    pub id: u64,
    pub basename: Option<String>,
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Pat {
    PConstant(Literal),
    PBound(PBound),
    PIgnored,
    POpen(POpen),
    PAdt(AdtPat),
}

#[derive(Debug, Clone, Deserialize)]
pub struct PBound {
    pub var: Var,
    /// Always `null` on the wire (`mplace` is stripped); kept for shape.
    #[serde(default)]
    pub mplace: serde_json::Value,
}

#[derive(Debug, Clone, Deserialize)]
pub struct POpen {
    pub fvar: FVar,
    #[serde(default)]
    pub mplace: serde_json::Value,
}

#[derive(Debug, Clone, Deserialize)]
pub struct AdtPat {
    pub variant_id: Option<u64>,
    pub fields: Vec<TPat>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TPat {
    pub pat: Pat,
    pub ty: Ty,
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
pub struct LambdaPayload {
    pub pat: TPat,
    pub body: Box<TExpr>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LetPayload {
    pub monadic: bool,
    pub pat: TPat,
    pub bound: Box<TExpr>,
    pub body: Box<TExpr>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SwitchPayload {
    pub scrutinee: Box<TExpr>,
    pub body: SwitchBody,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum SwitchBody {
    If(Box<SwitchIf>),
    Match(Vec<MatchBranch>),
}

#[derive(Debug, Clone, Deserialize)]
pub struct SwitchIf {
    pub then_branch: TExpr,
    pub else_branch: TExpr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MatchBranch {
    pub pat: TPat,
    pub branch: TExpr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Loop {
    pub loop_id: u64,
    pub span: Span,
    pub output_tys: Vec<Ty>,
    pub num_output_values: u32,
    pub inputs: Vec<TExpr>,
    pub num_input_conts: u32,
    pub loop_body: LoopBody,
    pub to_rec: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LoopBody {
    pub inputs: Vec<TPat>,
    pub loop_body: Box<TExpr>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct StructUpdate {
    pub struct_id: TypeId,
    pub init: Option<Box<TExpr>>,
    pub updates: Vec<StructUpdateField>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct StructUpdateField {
    pub field_id: u64,
    pub expr: TExpr,
}

/// Charon `field_proj_kind` — either an ADT field (with type-decl id +
/// optional variant) or a tuple projection (carrying the tuple arity).
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum FieldProjKind {
    ProjAdt(ProjAdtPayload),
    ProjTuple(u32),
}

#[derive(Debug, Clone, Deserialize)]
pub struct ProjAdtPayload {
    pub type_decl_id: u64,
    pub variant_id: Option<u64>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MProjectionElem {
    pub pkind: FieldProjKind,
    pub field_id: u64,
}

/// Charon meta-place — source-level provenance for a value. Recursive
/// via `PlaceProjection`. v2 ships the full structural payload (v1
/// emitted `null`).
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum MPlace {
    PlaceLocal(PlaceLocalPayload),
    PlaceGlobal(GlobalDeclRef),
    PlaceProjection(Box<PlaceProjectionPayload>),
}

#[derive(Debug, Clone, Deserialize)]
pub struct PlaceLocalPayload {
    pub local_id: u64,
    pub name: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PlaceProjectionPayload {
    pub parent: MPlace,
    pub elem: MProjectionElem,
}

/// Meta-info attached to an expression. v2 ships the full structural
/// payload of each variant (v1 summarised by tag).
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum EMeta {
    Assignment(Box<AssignmentMeta>),
    SymbolicAssignments(Vec<SymbolicAssignment>),
    SymbolicPlaces(Vec<SymbolicPlace>),
    MPlace(MPlace),
    Tag(String),
    TypeAnnot,
}

#[derive(Debug, Clone, Deserialize)]
pub struct AssignmentMeta {
    pub dst: MPlace,
    pub value: TExpr,
    pub origin: Option<MPlace>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SymbolicAssignment {
    pub mvar: TExpr,
    pub value: TExpr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SymbolicPlace {
    pub mvar: TExpr,
    pub name: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MetaPayload {
    pub meta: EMeta,
    pub expr: Box<TExpr>,
}

/// `EError`'s span + diagnostic message. v2 carries the source span;
/// v1 stripped it.
#[derive(Debug, Clone, Deserialize)]
pub struct EErrorPayload {
    pub span: Option<Span>,
    pub message: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum Expr {
    FVar(u64),
    BVar(BVar),
    CVar(u64),
    Const(Literal),
    App(App),
    Lambda(Box<LambdaPayload>),
    Qualif(Qualif),
    Let(Box<LetPayload>),
    Switch(Box<SwitchPayload>),
    Loop(Box<Loop>),
    StructUpdate(StructUpdate),
    Meta(MetaPayload),
    EError(EErrorPayload),
}

#[derive(Debug, Clone, Deserialize)]
pub struct TExpr {
    pub e: Expr,
    pub ty: Ty,
}

// ---------- Signatures, bodies, declarations ----------

#[derive(Debug, Clone, Deserialize)]
pub enum Explicit {
    Explicit,
    Implicit,
}

#[derive(Debug, Clone, Deserialize)]
pub enum Known {
    Known,
    Unknown,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ExplicitInfo {
    pub explicit_types: Vec<Explicit>,
    pub explicit_const_generics: Vec<Explicit>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct KnownInfo {
    pub known_types: Vec<Known>,
    pub known_const_generics: Vec<Known>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunEffectInfo {
    pub can_fail: bool,
    pub can_diverge: bool,
    pub is_rec: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunSigInfo {
    pub effect_info: FunEffectInfo,
    pub ignore_output: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BackEffectEntry {
    pub region_group_id: u32,
    pub effect_info: FunEffectInfo,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunSig {
    pub generics: GenericParams,
    pub explicit_info: ExplicitInfo,
    pub known_from_trait_refs: KnownInfo,
    pub preds: Predicates,
    pub inputs: Vec<Ty>,
    pub output: Ty,
    pub fwd_info: FunSigInfo,
    pub back_effect_info: Vec<BackEffectEntry>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunBody {
    pub inputs: Vec<TPat>,
    pub body: TExpr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BackendAttributes {
    pub reducible: bool,
}

/// Summarised `Charon` item source — we keep only the tag.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum ItemSource {
    TopLevelItem,
    ClosureItem,
    TraitDeclItem,
    TraitImplItem,
    OtherItemSource,
}

/// Summarised builtin-info payloads; the OCaml side ships them as a
/// single tag because no consumer needs their internal structure yet.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum BuiltinFunInfoSummary {
    BuiltinFunInfo,
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunDecl {
    pub def_id: u64,
    pub item_meta: ItemMeta,
    pub builtin_info: Option<BuiltinFunInfoSummary>,
    pub src: ItemSource,
    pub backend_attributes: BackendAttributes,
    pub num_loops: u32,
    pub loop_id: Option<LoopMarker>,
    pub loop_pos: Vec<u32>,
    pub name: String,
    pub signature: FunSig,
    pub is_global_decl_body: bool,
    pub body: Option<FunBody>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Field {
    pub field_name: Option<String>,
    pub field_ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Variant {
    pub variant_name: String,
    pub fields: Vec<Field>,
    pub discriminant: i64,
    pub ty: LiteralType,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", content = "payload")]
pub enum TypeDeclKind {
    Struct(Vec<Field>),
    Enum(Vec<Variant>),
    Opaque,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TypeDecl {
    pub def_id: u64,
    pub name: String,
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    pub explicit_info: ExplicitInfo,
    pub kind: TypeDeclKind,
    pub preds: Predicates,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GlobalDecl {
    pub def_id: u64,
    pub name: String,
    pub span: Span,
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    pub explicit_info: ExplicitInfo,
    pub preds: Predicates,
    pub ty: Ty,
    pub output_ty: Ty,
    pub can_fail: bool,
    pub src: ItemSource,
    pub body_id: u64,
}

/// `'a binder` — a value bundled with its own generic parameters.
#[derive(Debug, Clone, Deserialize)]
pub struct Binder<T> {
    pub binder_value: T,
    pub binder_generics: GenericParams,
    pub binder_preds: Predicates,
    pub binder_explicit_info: ExplicitInfo,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDeclConst {
    pub assoc_const_id: u64,
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDeclType {
    pub assoc_type_id: u64,
    pub name: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDeclMethod {
    pub method_id: u64,
    pub name: String,
    pub binder: Binder<FunDeclRef>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitDecl {
    pub def_id: u64,
    pub name: String,
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    pub explicit_info: ExplicitInfo,
    pub preds: Predicates,
    pub parent_clauses: Vec<TraitParam>,
    pub consts: Vec<TraitDeclConst>,
    pub types: Vec<TraitDeclType>,
    pub methods: Vec<TraitDeclMethod>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitImplConst {
    pub assoc_const_id: u64,
    pub name: String,
    pub global_ref: GlobalDeclRef,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitImplType {
    pub assoc_type_id: u64,
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TraitImpl {
    pub def_id: u64,
    pub name: String,
    pub item_meta: ItemMeta,
    pub impl_trait: TraitDeclRef,
    pub generics: GenericParams,
    pub explicit_info: ExplicitInfo,
    pub preds: Predicates,
    pub parent_trait_refs: Vec<TraitRef>,
    pub consts: Vec<TraitImplConst>,
    pub types: Vec<TraitImplType>,
    pub methods: Vec<TraitDeclMethod>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TranslatedCrate {
    pub pure_ir_fmt_version: u32,
    pub stage: String,
    pub crate_name: String,
    pub type_decls: Vec<TypeDecl>,
    pub fun_decls: Vec<FunDecl>,
    pub global_decls: Vec<GlobalDecl>,
    pub trait_decls: Vec<TraitDecl>,
    pub trait_impls: Vec<TraitImpl>,
}
