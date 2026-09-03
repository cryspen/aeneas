//! Failure isolation: function-list bisection (ddmin) + statement-level
//! reduction, both budget-bounded and preserving an exact failure fingerprint.
//!
//! The core algorithms ([`ddmin`], [`reduce_fn`]) are pure and take a predicate
//! closure, so they are unit-tested against a mocked pipeline. The pipeline-
//! backed drivers ([`bisect_functions`], [`reduce_culprit`]) wire them to the
//! real [`Pipeline`].

use anyhow::Result;
use syn::visit_mut::VisitMut;
use syn::{Expr, ItemFn};

use crate::corpus::{self, PackInput};
use crate::oracle::{Fingerprint, Verdict};
use crate::pipeline::{Pipeline, PipelineOpts};
use crate::triage::fingerprint_matches;

// ---------------------------------------------------------------------------
// Delta debugging (ddmin) over a set of items
// ---------------------------------------------------------------------------

fn split(items: &[usize], n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let len = items.len();
    let n = n.max(1).min(len.max(1));
    for i in 0..n {
        let start = i * len / n;
        let end = (i + 1) * len / n;
        if start < end {
            out.push(items[start..end].to_vec());
        }
    }
    out
}

/// Classic ddmin: return a minimal subset (as indices into the *input list*)
/// that still satisfies `still_fails`. Assumes `still_fails(all)` is true.
pub fn ddmin(n_items: usize, mut still_fails: impl FnMut(&[usize]) -> bool) -> Vec<usize> {
    let mut cfg: Vec<usize> = (0..n_items).collect();
    if cfg.len() <= 1 {
        return cfg;
    }
    let mut granularity = 2;
    while cfg.len() >= 2 {
        let subsets = split(&cfg, granularity);
        let mut reduced = false;

        // Try to reduce to a single subset.
        for s in &subsets {
            if s.len() < cfg.len() && still_fails(s) {
                cfg = s.clone();
                granularity = 2;
                reduced = true;
                break;
            }
        }

        // Otherwise try complements.
        if !reduced {
            for s in &subsets {
                let comp: Vec<usize> = cfg.iter().filter(|x| !s.contains(x)).cloned().collect();
                if !comp.is_empty() && comp.len() < cfg.len() && still_fails(&comp) {
                    cfg = comp;
                    granularity = (granularity - 1).max(2);
                    reduced = true;
                    break;
                }
            }
        }

        if !reduced {
            if granularity >= cfg.len() {
                break;
            }
            granularity = (granularity * 2).min(cfg.len());
        }
    }
    cfg
}

// ---------------------------------------------------------------------------
// Statement-level reduction on a single function
// ---------------------------------------------------------------------------

/// Greedily simplify `func`, keeping only reductions for which `still_fails`
/// stays true. Budget bounds the number of predicate evaluations.
pub fn reduce_fn(
    func: &ItemFn,
    budget: usize,
    mut still_fails: impl FnMut(&ItemFn) -> bool,
) -> ItemFn {
    let mut current = func.clone();
    let mut used = 0usize;

    loop {
        let mut improved = false;
        // Generate candidates lazily by kind, cheapest/most-effective first.
        let candidates = candidate_reductions(&current);
        for cand in candidates {
            if used >= budget {
                return current;
            }
            used += 1;
            if still_fails(&cand) {
                current = cand;
                improved = true;
                break;
            }
        }
        if !improved || used >= budget {
            break;
        }
    }
    current
}

/// Produce all single-step reductions of `f`, in priority order.
fn candidate_reductions(f: &ItemFn) -> Vec<ItemFn> {
    let mut out = Vec::new();
    // 1. remove one statement
    let n_stmts = count_stmts(f);
    for i in 0..n_stmts {
        if let Some(g) = remove_nth_stmt(f, i) {
            out.push(g);
        }
    }
    // 2. drop else branches
    let n_else = count_ifs_with_else(f);
    for i in 0..n_else {
        if let Some(g) = drop_nth_else(f, i) {
            out.push(g);
        }
    }
    // 3. collapse an if to its then-branch (unwrap conditional)
    for i in 0..n_else {
        if let Some(g) = collapse_nth_if(f, i) {
            out.push(g);
        }
    }
    // 4. replace a compound expr with Default::default()
    let n_expr = count_reducible_exprs(f);
    for i in 0..n_expr {
        if let Some(g) = replace_nth_expr_default(f, i) {
            out.push(g);
        }
    }
    out
}

// -- statement counting / removal --

struct StmtCounter {
    count: usize,
}
impl<'ast> syn::visit::Visit<'ast> for StmtCounter {
    fn visit_block(&mut self, b: &'ast syn::Block) {
        self.count += b.stmts.len();
        syn::visit::visit_block(self, b);
    }
}
fn count_stmts(f: &ItemFn) -> usize {
    let mut c = StmtCounter { count: 0 };
    syn::visit::Visit::visit_item_fn(&mut c, f);
    c.count
}

struct StmtRemover {
    target: usize,
    counter: usize,
    done: bool,
}
impl VisitMut for StmtRemover {
    fn visit_block_mut(&mut self, b: &mut syn::Block) {
        // recurse first so inner blocks get consistent numbering with counter
        if self.done {
            return;
        }
        let base = self.counter;
        let n = b.stmts.len();
        if self.target >= base && self.target < base + n {
            let idx = self.target - base;
            self.counter += n;
            b.stmts.remove(idx);
            self.done = true;
            return;
        }
        self.counter += n;
        syn::visit_mut::visit_block_mut(self, b);
    }
}
fn remove_nth_stmt(f: &ItemFn, n: usize) -> Option<ItemFn> {
    let mut g = f.clone();
    let mut r = StmtRemover {
        target: n,
        counter: 0,
        done: false,
    };
    r.visit_item_fn_mut(&mut g);
    if r.done {
        Some(g)
    } else {
        None
    }
}

// -- if/else --

struct IfElseCounter {
    count: usize,
}
impl<'ast> syn::visit::Visit<'ast> for IfElseCounter {
    fn visit_expr(&mut self, e: &'ast Expr) {
        if matches!(e, Expr::If(i) if i.else_branch.is_some()) {
            self.count += 1;
        }
        syn::visit::visit_expr(self, e);
    }
}
fn count_ifs_with_else(f: &ItemFn) -> usize {
    let mut c = IfElseCounter { count: 0 };
    syn::visit::Visit::visit_item_fn(&mut c, f);
    c.count
}

struct ElseDropper {
    target: usize,
    counter: usize,
    done: bool,
}
impl VisitMut for ElseDropper {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if self.done {
            return;
        }
        if let Expr::If(i) = e {
            if i.else_branch.is_some() {
                if self.counter == self.target {
                    i.else_branch = None;
                    self.done = true;
                    return;
                }
                self.counter += 1;
            }
        }
        syn::visit_mut::visit_expr_mut(self, e);
    }
}
fn drop_nth_else(f: &ItemFn, n: usize) -> Option<ItemFn> {
    let mut g = f.clone();
    let mut r = ElseDropper {
        target: n,
        counter: 0,
        done: false,
    };
    r.visit_item_fn_mut(&mut g);
    if r.done {
        Some(g)
    } else {
        None
    }
}

struct IfCollapser {
    target: usize,
    counter: usize,
    done: bool,
}
impl VisitMut for IfCollapser {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if self.done {
            return;
        }
        if let Expr::If(i) = e {
            if i.else_branch.is_some() {
                if self.counter == self.target {
                    let then = i.then_branch.clone();
                    *e = Expr::Block(syn::ExprBlock {
                        attrs: vec![],
                        label: None,
                        block: then,
                    });
                    self.done = true;
                    return;
                }
                self.counter += 1;
            }
        }
        syn::visit_mut::visit_expr_mut(self, e);
    }
}
fn collapse_nth_if(f: &ItemFn, n: usize) -> Option<ItemFn> {
    let mut g = f.clone();
    let mut r = IfCollapser {
        target: n,
        counter: 0,
        done: false,
    };
    r.visit_item_fn_mut(&mut g);
    if r.done {
        Some(g)
    } else {
        None
    }
}

// -- expr -> default --

fn is_reducible_expr(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Binary(_) | Expr::Call(_) | Expr::MethodCall(_) | Expr::Macro(_)
    )
}
struct ReducibleCounter {
    count: usize,
}
impl<'ast> syn::visit::Visit<'ast> for ReducibleCounter {
    fn visit_expr(&mut self, e: &'ast Expr) {
        if is_reducible_expr(e) {
            self.count += 1;
        }
        syn::visit::visit_expr(self, e);
    }
}
fn count_reducible_exprs(f: &ItemFn) -> usize {
    let mut c = ReducibleCounter { count: 0 };
    syn::visit::Visit::visit_item_fn(&mut c, f);
    c.count
}
struct ExprDefaulter {
    target: usize,
    counter: usize,
    done: bool,
}
impl VisitMut for ExprDefaulter {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if self.done {
            return;
        }
        if is_reducible_expr(e) {
            if self.counter == self.target {
                *e = syn::parse_quote!(Default::default());
                self.done = true;
                return;
            }
            self.counter += 1;
        }
        syn::visit_mut::visit_expr_mut(self, e);
    }
}
fn replace_nth_expr_default(f: &ItemFn, n: usize) -> Option<ItemFn> {
    let mut g = f.clone();
    let mut r = ExprDefaulter {
        target: n,
        counter: 0,
        done: false,
    };
    r.visit_item_fn_mut(&mut g);
    if r.done {
        Some(g)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Pipeline-backed drivers
// ---------------------------------------------------------------------------

/// Does running `subset` reproduce a crash matching `target` (within `tol`)?
fn subset_reproduces(
    pipeline: &Pipeline,
    inputs: &[PackInput],
    subset: &[usize],
    target: &Fingerprint,
    tol: u32,
    opts: &PipelineOpts,
    crate_id: &str,
) -> Result<bool> {
    let chosen: Vec<PackInput> = subset.iter().map(|&i| inputs[i].clone()).collect();
    if chosen.is_empty() {
        return Ok(false);
    }
    let (res, _pack) = pipeline.run_pack(&chosen, crate_id, opts)?;
    Ok(matches_target(&res.verdict, target, tol))
}

fn matches_target(verdict: &Option<Verdict>, target: &Fingerprint, tol: u32) -> bool {
    match verdict {
        Some(Verdict::Crash { fingerprint }) => fingerprint_matches(fingerprint, target, tol),
        _ => false,
    }
}

/// Bisect a failing pack to a minimal subset of functions that still reproduces
/// `target`. Returns original-input indices.
pub fn bisect_functions(
    pipeline: &Pipeline,
    inputs: &[PackInput],
    target: &Fingerprint,
    tol: u32,
    opts: &PipelineOpts,
) -> Result<Vec<usize>> {
    let mut counter = 0usize;
    let mut error: Option<anyhow::Error> = None;
    let minimal = ddmin(inputs.len(), |subset| {
        if error.is_some() {
            return false;
        }
        counter += 1;
        let crate_id = format!("bisect-{counter:04}");
        match subset_reproduces(pipeline, inputs, subset, target, tol, opts, &crate_id) {
            Ok(b) => b,
            Err(e) => {
                error = Some(e);
                false
            }
        }
    });
    if let Some(e) = error {
        return Err(e);
    }
    Ok(minimal)
}

/// Statement-reduce the single culprit function, keeping the fingerprint.
/// `base` is the (already minimized) set of inputs; `culprit` indexes into it.
pub fn reduce_culprit(
    pipeline: &Pipeline,
    base: &[PackInput],
    culprit: usize,
    target: &Fingerprint,
    tol: u32,
    budget: usize,
    opts: &PipelineOpts,
) -> Result<ItemFn> {
    let original = base[culprit].unit.func.clone();
    let mut counter = 0usize;
    let mut error: Option<anyhow::Error> = None;

    let reduced = reduce_fn(&original, budget, |cand| {
        if error.is_some() {
            return false;
        }
        counter += 1;
        let mut trial = base[culprit].clone();
        trial.unit.func = cand.clone();
        let crate_id = format!("reduce-{counter:04}");
        match pipeline.run_pack(std::slice::from_ref(&trial), &crate_id, opts) {
            Ok((res, _)) => matches_target(&res.verdict, target, tol),
            Err(e) => {
                error = Some(e);
                false
            }
        }
    });
    if let Some(e) = error {
        return Err(e);
    }
    Ok(reduced)
}

/// Render a reduced function as a standalone minimized `.rs` source (with the
/// unit's support items), for repro emission.
pub fn render_min_source(input: &PackInput, reduced: &ItemFn) -> String {
    let mut out = String::new();
    out.push_str("// Minimized reproducer (auto-generated).\n");
    for c in &input.unit.support {
        out.push_str(&c.text);
        out.push_str("\n\n");
    }
    out.push_str(&corpus::render_primary(reduced, &input.unit.orig_name));
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ddmin_isolates_single_culprit() {
        // Item 3 is the culprit: any subset containing it "fails".
        let minimal = ddmin(8, |subset| subset.contains(&3));
        assert_eq!(minimal, vec![3]);
    }

    #[test]
    fn ddmin_isolates_pair() {
        // Failure needs BOTH 2 and 5 present.
        let minimal = ddmin(8, |subset| subset.contains(&2) && subset.contains(&5));
        let set: std::collections::BTreeSet<_> = minimal.iter().cloned().collect();
        assert!(set.contains(&2) && set.contains(&5));
        assert_eq!(minimal.len(), 2, "should minimize to exactly the pair");
    }

    #[test]
    fn ddmin_all_needed() {
        let minimal = ddmin(4, |subset| subset.len() == 4);
        assert_eq!(minimal.len(), 4);
    }

    #[test]
    fn reduce_fn_strips_irrelevant_statements() {
        // Culprit shape: reproduces as long as the function still contains a
        // `loop` with a `return` inside (a stand-in for the F4 trigger).
        let f: ItemFn = syn::parse_str(
            "fn f(x: &mut u32) -> u32 {
                let a = 1;
                let b = a + 2;
                let c = b * 3;
                loop { if *x > 0 { return *x; } *x += 1; }
            }",
        )
        .unwrap();
        let still_fails = |g: &ItemFn| {
            use quote::ToTokens;
            let s = g.to_token_stream().to_string();
            s.contains("loop") && s.contains("return")
        };
        let reduced = reduce_fn(&f, 200, still_fails);
        use quote::ToTokens;
        let s = reduced.to_token_stream().to_string();
        assert!(s.contains("loop") && s.contains("return"));
        // the three irrelevant lets should be gone
        assert!(!s.contains("let a"), "reduced: {s}");
        assert!(still_fails(&reduced));
    }
}
