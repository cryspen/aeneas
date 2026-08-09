//! Source-level mutators (phase 1).
//!
//! Every mutator is a named [`Mutator`] variant, operates on a `syn` AST (so the
//! result is always re-parseable), and is driven by a seeded RNG. A mutation
//! *chain* of configurable depth is applied per function per round; the applied
//! variant names are recorded in provenance.

use rand::Rng;
use rand_chacha::ChaCha8Rng;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{parse_quote, BinOp, Block, Expr, ExprLit, ItemFn, Lit, LitInt, ReturnType, Stmt, Type};

/// The mutator catalogue (matches `fuzz/DESIGN.md`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutator {
    BorrowFlip,
    OpSwap,
    CmpFlip,
    BoundNudge,
    IntEdge,
    StmtDup,
    StmtSwap,
    StmtDelete,
    WrapLoopBreak,
    EarlyReturnInLoop,
    IfToMatchBool,
    LetSplit,
    SharedBorrowReassign,
    ReturnBorrowInLoop,
}

impl Mutator {
    pub fn name(&self) -> &'static str {
        match self {
            Mutator::BorrowFlip => "BorrowFlip",
            Mutator::OpSwap => "OpSwap",
            Mutator::CmpFlip => "CmpFlip",
            Mutator::BoundNudge => "BoundNudge",
            Mutator::IntEdge => "IntEdge",
            Mutator::StmtDup => "StmtDup",
            Mutator::StmtSwap => "StmtSwap",
            Mutator::StmtDelete => "StmtDelete",
            Mutator::WrapLoopBreak => "WrapLoopBreak",
            Mutator::EarlyReturnInLoop => "EarlyReturnInLoop",
            Mutator::IfToMatchBool => "IfToMatchBool",
            Mutator::LetSplit => "LetSplit",
            Mutator::SharedBorrowReassign => "SharedBorrowReassign",
            Mutator::ReturnBorrowInLoop => "ReturnBorrowInLoop",
        }
    }

    pub const ALL: &'static [Mutator] = &[
        Mutator::BorrowFlip,
        Mutator::OpSwap,
        Mutator::CmpFlip,
        Mutator::BoundNudge,
        Mutator::IntEdge,
        Mutator::StmtDup,
        Mutator::StmtSwap,
        Mutator::StmtDelete,
        Mutator::WrapLoopBreak,
        Mutator::EarlyReturnInLoop,
        Mutator::IfToMatchBool,
        Mutator::LetSplit,
        Mutator::SharedBorrowReassign,
        Mutator::ReturnBorrowInLoop,
    ];

    /// Apply this mutator to `f`. Returns true if a site was found and mutated.
    pub fn apply(&self, f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
        match self {
            Mutator::BorrowFlip => borrow_flip(f, rng),
            Mutator::OpSwap => op_swap(f, rng),
            Mutator::CmpFlip => cmp_flip(f, rng),
            Mutator::BoundNudge => bound_nudge(f, rng),
            Mutator::IntEdge => int_edge(f, rng),
            Mutator::StmtDup => stmt_dup(f, rng),
            Mutator::StmtSwap => stmt_swap(f, rng),
            Mutator::StmtDelete => stmt_delete(f, rng),
            Mutator::WrapLoopBreak => wrap_loop_break(f),
            Mutator::EarlyReturnInLoop => early_return_in_loop(f, rng),
            Mutator::IfToMatchBool => if_to_match_bool(f, rng),
            Mutator::LetSplit => let_split(f, rng),
            Mutator::SharedBorrowReassign => shared_borrow_reassign(f),
            Mutator::ReturnBorrowInLoop => return_borrow_in_loop(f),
        }
    }
}

/// Apply a chain of up to `depth` mutations to a function clone.
/// Returns the mutated function and the applied mutator names (in order).
pub fn mutate_chain(func: &ItemFn, rng: &mut ChaCha8Rng, depth: usize) -> (ItemFn, Vec<String>) {
    let mut f = func.clone();
    let mut applied = Vec::new();
    let max_attempts = depth.saturating_mul(8).max(8);
    let mut attempts = 0;
    while applied.len() < depth && attempts < max_attempts {
        attempts += 1;
        let idx = rng.random_range(0..Mutator::ALL.len());
        let m = Mutator::ALL[idx];
        if m.apply(&mut f, rng) {
            applied.push(m.name().to_string());
        }
    }
    (f, applied)
}

/// Pick a chain depth in `[min, max]` and mutate. Convenience for the campaign.
pub fn mutate_with_depth_range(
    func: &ItemFn,
    rng: &mut ChaCha8Rng,
    min: usize,
    max: usize,
) -> (ItemFn, Vec<String>) {
    let depth = if max <= min {
        min.max(1)
    } else {
        rng.random_range(min..=max)
    };
    mutate_chain(func, rng, depth)
}

// ---------------------------------------------------------------------------
// Generic count/apply framework
// ---------------------------------------------------------------------------

struct ExprCounter<S: Fn(&Expr) -> bool> {
    is_site: S,
    count: usize,
}
impl<'ast, S: Fn(&Expr) -> bool> Visit<'ast> for ExprCounter<S> {
    fn visit_expr(&mut self, e: &'ast Expr) {
        if (self.is_site)(e) {
            self.count += 1;
        }
        syn::visit::visit_expr(self, e);
    }
}

struct ExprApplier<'a, S: Fn(&Expr) -> bool, M: FnMut(&mut Expr, &mut ChaCha8Rng) -> bool> {
    is_site: S,
    mutate: M,
    target: usize,
    counter: usize,
    applied: bool,
    rng: &'a mut ChaCha8Rng,
}
impl<'a, S: Fn(&Expr) -> bool, M: FnMut(&mut Expr, &mut ChaCha8Rng) -> bool> VisitMut
    for ExprApplier<'a, S, M>
{
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if self.applied {
            return;
        }
        if (self.is_site)(e) {
            if self.counter == self.target {
                self.applied = (self.mutate)(e, self.rng);
                if self.applied {
                    return;
                }
                // mutate declined; keep walking as if not a site
                self.counter += 1;
                syn::visit_mut::visit_expr_mut(self, e);
                return;
            } else {
                self.counter += 1;
            }
        }
        syn::visit_mut::visit_expr_mut(self, e);
    }
}

fn walk_exprs(
    f: &mut ItemFn,
    rng: &mut ChaCha8Rng,
    is_site: impl Fn(&Expr) -> bool + Copy,
    mutate: impl FnMut(&mut Expr, &mut ChaCha8Rng) -> bool,
) -> bool {
    let total = {
        let mut c = ExprCounter { is_site, count: 0 };
        c.visit_item_fn(f);
        c.count
    };
    if total == 0 {
        return false;
    }
    let target = rng.random_range(0..total);
    let mut a = ExprApplier {
        is_site,
        mutate,
        target,
        counter: 0,
        applied: false,
        rng,
    };
    a.visit_item_fn_mut(f);
    a.applied
}

struct BlockCounter<S: Fn(&Block) -> bool> {
    is_site: S,
    count: usize,
}
impl<'ast, S: Fn(&Block) -> bool> Visit<'ast> for BlockCounter<S> {
    fn visit_block(&mut self, b: &'ast Block) {
        if (self.is_site)(b) {
            self.count += 1;
        }
        syn::visit::visit_block(self, b);
    }
}

struct BlockApplier<'a, S: Fn(&Block) -> bool, M: FnMut(&mut Block, &mut ChaCha8Rng) -> bool> {
    is_site: S,
    mutate: M,
    target: usize,
    counter: usize,
    applied: bool,
    rng: &'a mut ChaCha8Rng,
}
impl<'a, S: Fn(&Block) -> bool, M: FnMut(&mut Block, &mut ChaCha8Rng) -> bool> VisitMut
    for BlockApplier<'a, S, M>
{
    fn visit_block_mut(&mut self, b: &mut Block) {
        if self.applied {
            return;
        }
        // visit children first so counting order matches (pre-order on the block
        // itself, matching the immutable counter which also checks the node then
        // recurses).
        if (self.is_site)(b) {
            if self.counter == self.target {
                self.applied = (self.mutate)(b, self.rng);
                if self.applied {
                    return;
                }
                self.counter += 1;
            } else {
                self.counter += 1;
            }
        }
        syn::visit_mut::visit_block_mut(self, b);
    }
}

fn walk_blocks(
    f: &mut ItemFn,
    rng: &mut ChaCha8Rng,
    is_site: impl Fn(&Block) -> bool + Copy,
    mutate: impl FnMut(&mut Block, &mut ChaCha8Rng) -> bool,
) -> bool {
    let total = {
        let mut c = BlockCounter { is_site, count: 0 };
        c.visit_item_fn(f);
        c.count
    };
    if total == 0 {
        return false;
    }
    let target = rng.random_range(0..total);
    let mut a = BlockApplier {
        is_site,
        mutate,
        target,
        counter: 0,
        applied: false,
        rng,
    };
    a.visit_item_fn_mut(f);
    a.applied
}

// ---------------------------------------------------------------------------
// Individual mutators
// ---------------------------------------------------------------------------

fn is_ref_expr(e: &Expr) -> bool {
    matches!(e, Expr::Reference(_))
}

fn borrow_flip(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    // Prefer flipping an expression borrow; fall back to a type borrow.
    let flipped = walk_exprs(f, rng, is_ref_expr, |e, _| {
        if let Expr::Reference(r) = e {
            if r.mutability.is_some() {
                r.mutability = None;
            } else {
                r.mutability = Some(Default::default());
            }
            return true;
        }
        false
    });
    if flipped {
        return true;
    }
    // type-level &T <-> &mut T
    struct TyCount {
        count: usize,
    }
    impl<'ast> Visit<'ast> for TyCount {
        fn visit_type(&mut self, t: &'ast Type) {
            if matches!(t, Type::Reference(_)) {
                self.count += 1;
            }
            syn::visit::visit_type(self, t);
        }
    }
    let total = {
        let mut c = TyCount { count: 0 };
        c.visit_item_fn(f);
        c.count
    };
    if total == 0 {
        return false;
    }
    let target = rng.random_range(0..total);
    struct TyApply {
        target: usize,
        counter: usize,
        applied: bool,
    }
    impl VisitMut for TyApply {
        fn visit_type_mut(&mut self, t: &mut Type) {
            if self.applied {
                return;
            }
            if let Type::Reference(r) = t {
                if self.counter == self.target {
                    if r.mutability.is_some() {
                        r.mutability = None;
                    } else {
                        r.mutability = Some(Default::default());
                    }
                    self.applied = true;
                    return;
                }
                self.counter += 1;
            }
            syn::visit_mut::visit_type_mut(self, t);
        }
    }
    let mut a = TyApply {
        target,
        counter: 0,
        applied: false,
    };
    a.visit_item_fn_mut(f);
    a.applied
}

fn arith_method_swap(name: &str) -> Option<String> {
    for prefix in ["wrapping_", "checked_", "saturating_", "overflowing_"] {
        if let Some(op) = name.strip_prefix(prefix) {
            let new_op = match op {
                "add" => "sub",
                "sub" => "mul",
                "mul" => "add",
                _ => return None,
            };
            return Some(format!("{}{}", prefix, new_op));
        }
    }
    None
}

fn op_swap(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    fn is_site(e: &Expr) -> bool {
        match e {
            Expr::Binary(b) => matches!(b.op, BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_)),
            Expr::MethodCall(m) => arith_method_swap(&m.method.to_string()).is_some(),
            _ => false,
        }
    }
    walk_exprs(f, rng, is_site, |e, rng| match e {
        Expr::Binary(b) => {
            let choices: [BinOp; 3] = [
                BinOp::Add(Default::default()),
                BinOp::Sub(Default::default()),
                BinOp::Mul(Default::default()),
            ];
            let cur = match b.op {
                BinOp::Add(_) => 0,
                BinOp::Sub(_) => 1,
                _ => 2,
            };
            let mut pick = rng.random_range(0..3);
            if pick == cur {
                pick = (pick + 1) % 3;
            }
            b.op = choices[pick];
            true
        }
        Expr::MethodCall(m) => {
            if let Some(newname) = arith_method_swap(&m.method.to_string()) {
                m.method = syn::Ident::new(&newname, m.method.span());
                true
            } else {
                false
            }
        }
        _ => false,
    })
}

fn cmp_flip(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    fn is_site(e: &Expr) -> bool {
        matches!(e, Expr::Binary(b) if matches!(b.op,
            BinOp::Lt(_)|BinOp::Le(_)|BinOp::Gt(_)|BinOp::Ge(_)|BinOp::Eq(_)|BinOp::Ne(_)))
    }
    walk_exprs(f, rng, is_site, |e, rng| {
        if let Expr::Binary(b) = e {
            let choices: [BinOp; 6] = [
                BinOp::Lt(Default::default()),
                BinOp::Le(Default::default()),
                BinOp::Gt(Default::default()),
                BinOp::Ge(Default::default()),
                BinOp::Eq(Default::default()),
                BinOp::Ne(Default::default()),
            ];
            let cur = match b.op {
                BinOp::Lt(_) => 0,
                BinOp::Le(_) => 1,
                BinOp::Gt(_) => 2,
                BinOp::Ge(_) => 3,
                BinOp::Eq(_) => 4,
                _ => 5,
            };
            let mut pick = rng.random_range(0..6);
            if pick == cur {
                pick = (pick + 1) % 6;
            }
            b.op = choices[pick];
            return true;
        }
        false
    })
}

fn as_int_lit(e: &Expr) -> Option<&LitInt> {
    if let Expr::Lit(ExprLit {
        lit: Lit::Int(li), ..
    }) = e
    {
        Some(li)
    } else {
        None
    }
}

fn bound_nudge(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    walk_exprs(
        f,
        rng,
        |e| as_int_lit(e).is_some(),
        |e, rng| {
            if let Some(li) = as_int_lit(e) {
                let suffix = li.suffix().to_string();
                let digits = li.base10_digits().to_string();
                let val: i128 = match digits.parse() {
                    Ok(v) => v,
                    Err(_) => return false,
                };
                let up = rng.random_bool(0.5);
                let newval = if val <= 0 { val + 1 } else if up { val + 1 } else { val - 1 };
                let newlit = LitInt::new(&format!("{}{}", newval, suffix), li.span());
                *e = Expr::Lit(ExprLit {
                    attrs: vec![],
                    lit: Lit::Int(newlit),
                });
                return true;
            }
            false
        },
    )
}

fn int_edge(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    walk_exprs(
        f,
        rng,
        |e| as_int_lit(e).is_some(),
        |e, rng| {
            let (suffix, span) = match as_int_lit(e) {
                Some(li) => (li.suffix().to_string(), li.span()),
                None => return false,
            };
            // edge selection
            let has_suffix = !suffix.is_empty();
            let choices: &[&str] = if has_suffix {
                &["0", "1", "MAX", "MIN", "MAX-1"]
            } else {
                &["0", "1"]
            };
            let pick = choices[rng.random_range(0..choices.len())];
            let new_expr: Expr = match pick {
                "0" => Expr::Lit(ExprLit {
                    attrs: vec![],
                    lit: Lit::Int(LitInt::new(&format!("0{}", suffix), span)),
                }),
                "1" => Expr::Lit(ExprLit {
                    attrs: vec![],
                    lit: Lit::Int(LitInt::new(&format!("1{}", suffix), span)),
                }),
                "MAX" => match syn::parse_str::<Expr>(&format!("({}::MAX)", suffix)) {
                    Ok(x) => x,
                    Err(_) => return false,
                },
                "MIN" => match syn::parse_str::<Expr>(&format!("({}::MIN)", suffix)) {
                    Ok(x) => x,
                    Err(_) => return false,
                },
                "MAX-1" => match syn::parse_str::<Expr>(&format!("({}::MAX - 1)", suffix)) {
                    Ok(x) => x,
                    Err(_) => return false,
                },
                _ => return false,
            };
            *e = new_expr;
            true
        },
    )
}

/// A statement that is only valid as the *last* statement of a block (a
/// trailing expression / macro without a semicolon). Moving it or appending
/// after it produces invalid syntax.
fn is_bare_trailing(s: &Stmt) -> bool {
    match s {
        Stmt::Expr(_, None) => true,
        Stmt::Macro(m) => m.semi_token.is_none(),
        _ => false,
    }
}

fn dup_ok(s: &Stmt) -> bool {
    !is_bare_trailing(s)
        && matches!(s, Stmt::Local(_) | Stmt::Macro(_) | Stmt::Expr(_, Some(_)))
}

fn stmt_dup(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    walk_blocks(
        f,
        rng,
        |b| b.stmts.iter().any(dup_ok),
        |b, rng| {
            let idxs: Vec<usize> = b
                .stmts
                .iter()
                .enumerate()
                .filter(|(_, s)| dup_ok(s))
                .map(|(i, _)| i)
                .collect();
            if idxs.is_empty() {
                return false;
            }
            let i = idxs[rng.random_range(0..idxs.len())];
            let clone = b.stmts[i].clone();
            b.stmts.insert(i + 1, clone);
            true
        },
    )
}

fn swappable_positions(b: &Block) -> Vec<usize> {
    // positions i where neither stmts[i] nor stmts[i+1] is a bare trailing stmt
    // (so the swap keeps the block well-formed).
    (0..b.stmts.len().saturating_sub(1))
        .filter(|&i| !is_bare_trailing(&b.stmts[i]) && !is_bare_trailing(&b.stmts[i + 1]))
        .collect()
}

fn stmt_swap(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    walk_blocks(
        f,
        rng,
        |b| !swappable_positions(b).is_empty(),
        |b, rng| {
            let pos = swappable_positions(b);
            if pos.is_empty() {
                return false;
            }
            let i = pos[rng.random_range(0..pos.len())];
            b.stmts.swap(i, i + 1);
            true
        },
    )
}

fn stmt_delete(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    walk_blocks(
        f,
        rng,
        |b| !b.stmts.is_empty(),
        |b, rng| {
            if b.stmts.is_empty() {
                return false;
            }
            let i = rng.random_range(0..b.stmts.len());
            b.stmts.remove(i);
            true
        },
    )
}

fn wrap_loop_break(f: &mut ItemFn) -> bool {
    // Only safe when the function returns unit (else wrapping changes the type).
    if !matches!(f.sig.output, ReturnType::Default) {
        return false;
    }
    if f.block.stmts.is_empty() {
        return false;
    }
    // Avoid re-wrapping trivially.
    if let Some(Stmt::Expr(Expr::Loop(_), _)) = f.block.stmts.first() {
        if f.block.stmts.len() == 1 {
            return false;
        }
    }
    let mut stmts = f.block.stmts.clone();
    // A trailing semicolon-less statement can't be followed by `break;`; give it
    // a semicolon first.
    if let Some(last) = stmts.last_mut() {
        match last {
            Stmt::Expr(_, semi @ None) => *semi = Some(Default::default()),
            Stmt::Macro(m) if m.semi_token.is_none() => {
                m.semi_token = Some(Default::default())
            }
            _ => {}
        }
    }
    let new_block: Block = parse_quote!({
        loop {
            #(#stmts)*
            break;
        }
    });
    *f.block = new_block;
    true
}

fn early_return_in_loop(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    let unit = matches!(f.sig.output, ReturnType::Default);
    fn is_loopish(e: &Expr) -> bool {
        matches!(e, Expr::Loop(_) | Expr::While(_) | Expr::ForLoop(_))
    }
    walk_exprs(f, rng, is_loopish, move |e, _| {
        let guard: Stmt = if unit {
            parse_quote!(if false { return; })
        } else {
            parse_quote!(if false { return Default::default(); })
        };
        match e {
            Expr::Loop(l) => {
                l.body.stmts.insert(0, guard);
                true
            }
            Expr::While(w) => {
                w.body.stmts.insert(0, guard);
                true
            }
            Expr::ForLoop(fl) => {
                fl.body.stmts.insert(0, guard);
                true
            }
            _ => false,
        }
    })
}

fn if_to_match_bool(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    fn is_site(e: &Expr) -> bool {
        matches!(e, Expr::If(i) if i.else_branch.is_some())
    }
    walk_exprs(f, rng, is_site, |e, _| {
        if let Expr::If(i) = e {
            let cond = (*i.cond).clone();
            let then_block = &i.then_branch;
            let else_expr = match &i.else_branch {
                Some((_, be)) => (**be).clone(),
                None => return false,
            };
            let new: Expr = parse_quote!(match #cond {
                true => #then_block,
                false => #else_expr,
            });
            *e = new;
            return true;
        }
        false
    })
}

fn let_split(f: &mut ItemFn, rng: &mut ChaCha8Rng) -> bool {
    fn local_binary_idx(b: &Block) -> Vec<usize> {
        b.stmts
            .iter()
            .enumerate()
            .filter(|(_, s)| {
                if let Stmt::Local(l) = s {
                    if let Some(init) = &l.init {
                        return matches!(&*init.expr, Expr::Binary(_)) && init.diverge.is_none();
                    }
                }
                false
            })
            .map(|(i, _)| i)
            .collect()
    }
    walk_blocks(
        f,
        rng,
        |b| !local_binary_idx(b).is_empty(),
        |b, rng| {
            let idxs = local_binary_idx(b);
            if idxs.is_empty() {
                return false;
            }
            let i = idxs[rng.random_range(0..idxs.len())];
            let tmp = format!("__ms_{}", rng.random_range(0..1_000_000u32));
            let tmp_id = syn::Ident::new(&tmp, proc_macro2::Span::call_site());
            if let Stmt::Local(l) = &b.stmts[i] {
                if let Some(init) = &l.init {
                    if let Expr::Binary(bin) = &*init.expr {
                        let lhs = (*bin.left).clone();
                        let op = bin.op;
                        let rhs = (*bin.right).clone();
                        let pat = l.pat.clone();
                        let tmp_local: Stmt = parse_quote!(let #tmp_id = #lhs;);
                        let new_local: Stmt = parse_quote!(let #pat = #tmp_id #op #rhs;);
                        b.stmts.splice(i..=i, [tmp_local, new_local]);
                        return true;
                    }
                }
            }
            false
        },
    )
}

/// Primitive integer type name, if `t` is one.
fn prim_int_name(t: &Type) -> Option<String> {
    if let Type::Path(tp) = t {
        if tp.qself.is_none() {
            if let Some(seg) = tp.path.segments.last() {
                let n = seg.ident.to_string();
                if matches!(
                    n.as_str(),
                    "u8" | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                ) {
                    return Some(n);
                }
            }
        }
    }
    None
}

/// A primitive-int reference parameter: `(name, prim-int, is_mut_ref)`.
/// Matches `x: &u32` and `x: &mut u32` and friends, with a simple binding name.
fn int_ref_param_info(pt: &syn::PatType) -> Option<(syn::Ident, String, bool)> {
    if let Type::Reference(r) = &*pt.ty {
        if let Some(prim) = prim_int_name(&r.elem) {
            if let syn::Pat::Ident(pi) = &*pt.pat {
                let n = pi.ident.to_string();
                if n != "_" {
                    return Some((pi.ident.clone(), prim, r.mutability.is_some()));
                }
            }
        }
    }
    None
}

/// The first primitive-int reference parameter of `f`, if any.
fn first_int_ref_param(f: &ItemFn) -> Option<(syn::Ident, String, bool)> {
    f.sig.inputs.iter().find_map(|input| match input {
        syn::FnArg::Typed(pt) => int_ref_param_info(pt),
        _ => None,
    })
}

/// A second primitive-int reference parameter of the same width as `prim`,
/// distinct from `exclude` — reused as the reassignment source `y` in the F6
/// shape when the seed already provides one.
fn second_int_ref_param(f: &ItemFn, exclude: &syn::Ident, prim: &str) -> Option<syn::Ident> {
    f.sig.inputs.iter().find_map(|input| match input {
        syn::FnArg::Typed(pt) => match int_ref_param_info(pt) {
            Some((name, p, _)) if &name != exclude && p == prim => Some(name),
            _ => None,
        },
        _ => None,
    })
}

/// F4 family: rewrite the function into a "return the deref of a `&mut` int
/// inside a single loop" shape. Fires on ANY function with a primitive-int
/// reference parameter (shared or mutable) — the parameter name `x` and the
/// referent's int width are taken from the seed, and the return type is morphed
/// to that int. The loop hands back `*x` as both the forward result and its
/// carried value, which is the F4 (PureMicroPassesLoops.ml:1818) trigger. A
/// shared `&PRIM` parameter is promoted to `&mut PRIM` as part of the rewrite.
fn return_borrow_in_loop(f: &mut ItemFn) -> bool {
    let (x, prim, _is_mut) = match first_int_ref_param(f) {
        Some(t) => t,
        None => return false,
    };
    let prim_ty = syn::Ident::new(&prim, proc_macro2::Span::call_site());
    let name = f.sig.ident.clone();
    let probe: ItemFn = parse_quote!(
        fn #name(#x: &mut #prim_ty) -> #prim_ty {
            loop {
                if *#x > 0 {
                    return *#x;
                }
                *#x = (*#x).wrapping_add(1);
            }
        }
    );
    f.sig = probe.sig;
    f.block = probe.block;
    true
}

/// F6 family: rewrite the function into a "reassign a shared borrow before a
/// loop that keeps a matchless shared loan alive" shape. Fires on ANY function
/// with a primitive-int reference parameter: that parameter becomes the
/// `mut`-bound shared borrow `x`, a second same-width int reference (reused from
/// the seed if it has one, else synthesized as `__ms_y`) becomes `y`, both share
/// an explicit lifetime, and the body does `let s = *x; x = y; loop { s += *x;
/// ... }`. The old loan of `x` left dangling by the reassignment is the F6
/// (InterpAbs.ml:1671) trigger. Parameterized by the seed's param name + width.
fn shared_borrow_reassign(f: &mut ItemFn) -> bool {
    let (x, prim, _is_mut) = match first_int_ref_param(f) {
        Some(t) => t,
        None => return false,
    };
    let prim_ty = syn::Ident::new(&prim, proc_macro2::Span::call_site());
    let y = second_int_ref_param(f, &x, &prim)
        .unwrap_or_else(|| syn::Ident::new("__ms_y", proc_macro2::Span::call_site()));
    let name = f.sig.ident.clone();
    let probe: ItemFn = parse_quote!(
        fn #name<'a>(mut #x: &'a #prim_ty, #y: &'a #prim_ty) -> #prim_ty {
            let mut __ms_s = *#x;
            #x = #y;
            let mut __ms_i = 0u32;
            loop {
                __ms_s = __ms_s.wrapping_add(*#x);
                __ms_i = __ms_i.wrapping_add(1);
                if __ms_i > 10 {
                    return __ms_s;
                }
            }
        }
    );
    f.sig = probe.sig;
    f.block = probe.block;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;
    use rand::SeedableRng;

    fn parse_fn(src: &str) -> ItemFn {
        syn::parse_str(src).unwrap()
    }

    /// Assert the mutated function re-parses as valid Rust.
    fn assert_reparses(f: &ItemFn) {
        let text = f.to_token_stream().to_string();
        syn::parse_str::<ItemFn>(&text)
            .unwrap_or_else(|e| panic!("mutated fn did not re-parse: {e}\n{text}"));
    }

    fn rng() -> ChaCha8Rng {
        ChaCha8Rng::seed_from_u64(12345)
    }

    #[test]
    fn each_mutator_produces_parseable_code() {
        // A function rich enough that most mutators find a site.
        let base = parse_fn(
            "fn g(x: &mut u32, y: &u32) -> () {
                let mut a = 1u32 + 2u32;
                let b = a * 3u32;
                if a > b { a = b; } else { a = 0; }
                while a < 10u32 { a = a.wrapping_add(1u32); }
                let mut z = &a;
            }",
        );
        for m in Mutator::ALL {
            let mut f = base.clone();
            let mut r = rng();
            let _ = m.apply(&mut f, &mut r);
            assert_reparses(&f);
        }
    }

    #[test]
    fn chain_is_deterministic_and_parseable() {
        let base = parse_fn(
            "fn h(a: u32, b: u32) -> u32 { let mut c = a + b; c = c * 2u32; c }",
        );
        let mut r1 = ChaCha8Rng::seed_from_u64(99);
        let (f1, chain1) = mutate_chain(&base, &mut r1, 3);
        let mut r2 = ChaCha8Rng::seed_from_u64(99);
        let (f2, chain2) = mutate_chain(&base, &mut r2, 3);
        assert_eq!(chain1, chain2, "same seed -> same chain");
        assert_eq!(
            f1.to_token_stream().to_string(),
            f2.to_token_stream().to_string()
        );
        assert_reparses(&f1);
    }

    #[test]
    fn return_borrow_in_loop_matches_f4_shape() {
        let base = parse_fn("fn f(x: &mut u32) -> u32 { *x }");
        let mut f = base.clone();
        assert!(Mutator::ReturnBorrowInLoop.apply(&mut f, &mut rng()));
        let text = f.to_token_stream().to_string();
        assert!(text.contains("loop"));
        assert!(text.contains("return"));
        assert_reparses(&f);
    }

    #[test]
    fn shared_borrow_reassign_fires() {
        let base = parse_fn(
            "fn f(mut x: &u32, y: &u32) -> u32 { let s = *x; loop { if *x > 0 { return s; } } }",
        );
        let mut f = base.clone();
        assert!(Mutator::SharedBorrowReassign.apply(&mut f, &mut rng()));
        assert_reparses(&f);
        assert!(f.to_token_stream().to_string().contains("x = y"));
    }

    #[test]
    fn if_to_match_bool_transforms() {
        let base = parse_fn("fn f(c: bool) -> u32 { if c { 1 } else { 2 } }");
        let mut f = base.clone();
        assert!(Mutator::IfToMatchBool.apply(&mut f, &mut rng()));
        assert!(f.to_token_stream().to_string().contains("match"));
        assert_reparses(&f);
    }
}
