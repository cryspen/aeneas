//! Phase-2 borrow-weighted grammar generator.
//!
//! Produces random-but-rustc-valid functions over the *safe supported subset*
//! of Rust that charon+aeneas accept: integers (all widths, incl.
//! wrapping/checked ops), `bool`, `char`, tuples, small structs/enums, fixed
//! arrays, and `&`/`&mut` references. It deliberately avoids trait objects,
//! closures, iterators/`collect`, and floats, and never emits range-`for` loops
//! (those lower to noncomputable `Step` axioms — see `fuzz/semdiff/RECIPE.md`).
//!
//! The distribution is weighted toward the borrow-heavy, bug-prone shapes from
//! `fuzz/DESIGN.md` and `06-bug-hunt-findings.md`: `&mut` returns + reborrow
//! chains, two-phase borrows, enums/structs carrying borrows matched in arms,
//! loops carrying borrows across iterations, return/break-with-value in loops
//! (F4 family), and shared-borrow reassignment before a loop (F6 family), plus
//! deep branching / nested matches before joins.
//!
//! Two generation modes:
//!   * **open** — free functions with *borrow parameters* and (often) borrow
//!     returns, fed through the existing pack/pipeline crash+reject oracles.
//!     Not executed, so they need only be rustc-valid.
//!   * **closed** — niladic deterministic `test_*` functions embedding
//!     `assert!`s, using `while`/index/`loop`-with-break loops (never range-for)
//!     with bounded iteration counts, for the semantic differential oracle. The
//!     borrow shapes are expressed over *local* borrows so the function stays
//!     `() -> ()`.
//!
//! The generator is a *template + typed-hole* design: a library of borrow-heavy
//! skeletons (each known borrow-check-valid) whose value holes are filled by a
//! small typed-expression generator that only references in-scope variables of
//! the active integer type and only uses total / wrapping operations. This keeps
//! the rustc yield very high while still exercising the translator's arithmetic,
//! branch, loop and borrow machinery. Everything is seeded (`rand_chacha`) and
//! reproducible from `(seed, index)`.

use std::path::Path;
use std::process::Command;

use rand::Rng;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::corpus::{self, Unit};

/// The integer types the generator ranges over (all widths, signed + unsigned).
pub const INT_TYPES: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

/// Crate-level `#![allow(...)]` header applied to every generated mini-crate so
/// benign warnings (dead code, unused, always-false comparisons on unsigned,
/// unreachable tails after diverging loops) never obscure a real rustc error.
pub const GEN_HEADER: &str = "#![allow(dead_code, unused_variables, unused_mut, unused_parens, unused_assignments, unused_comparisons, unreachable_code, unused_braces)]\n\n";

/// One generated open function: its rendered `fn` text plus any support items
/// (structs/enums/impls) it needs, each uniquely named by the function index.
struct OpenFn {
    support: Vec<String>,
    func: String,
}

/// One generated closed `test_*` function.
struct ClosedFn {
    name: String,
    support: Vec<String>,
    func: String,
}

/// The generator: a seeded RNG plus the shape weights.
pub struct Gen {
    rng: ChaCha8Rng,
}

impl Gen {
    pub fn new(seed: u64) -> Gen {
        Gen {
            rng: ChaCha8Rng::seed_from_u64(seed),
        }
    }

    // -- primitive pickers --------------------------------------------------

    fn int_ty(&mut self) -> &'static str {
        INT_TYPES[self.rng.random_range(0..INT_TYPES.len())]
    }

    /// A small integer literal for type `ty`. Always *type-suffixed* (`20u8`,
    /// `(-3i8)`, `(ty::MAX)`) so it anchors method resolution even in
    /// non-annotated contexts — `(20u32).wrapping_sub(5)` resolves, whereas an
    /// unsuffixed `(20).wrapping_sub(5)` is an ambiguous numeric type (E0689).
    /// Magnitudes stay ≤ 20 so no `overflowing_literals` occurs for any width;
    /// negatives are only produced for signed types and are parenthesized so
    /// they compose as method receivers.
    fn int_lit(&mut self, ty: &str) -> String {
        let signed = ty.starts_with('i');
        match self.rng.random_range(0..12u32) {
            0 => format!("({ty}::MAX)"),
            1 => format!("({ty}::MIN)"),
            _ => {
                const VALS: &[u32] = &[0, 1, 2, 3, 4, 5, 7, 10, 13, 20];
                let v = VALS[self.rng.random_range(0..VALS.len())];
                if signed && v != 0 && self.rng.random_bool(0.35) {
                    format!("(-{v}{ty})")
                } else {
                    format!("{v}{ty}")
                }
            }
        }
    }

    fn pick_var(&mut self, vars: &[String]) -> Option<String> {
        if vars.is_empty() {
            None
        } else {
            Some(vars[self.rng.random_range(0..vars.len())].clone())
        }
    }

    /// A typed integer expression of type `ty` over the in-scope `vars`. All
    /// literals are unsuffixed and infer `ty` from the enclosing annotated slot.
    /// Only total / wrapping operations are used (division is guarded nonzero and
    /// restricted to unsigned) so the expression always typechecks.
    fn int_expr(&mut self, vars: &[String], ty: &str, depth: usize) -> String {
        // Base case: a variable (preferred when available) or a literal.
        if depth == 0 {
            return match self.pick_var(vars) {
                Some(v) if self.rng.random_bool(0.6) => v,
                _ => self.int_lit(ty),
            };
        }
        let unsigned = ty.starts_with('u');
        let arms = if unsigned { 6 } else { 5 };
        match self.rng.random_range(0..arms) {
            0 => match self.pick_var(vars) {
                Some(v) if self.rng.random_bool(0.6) => v,
                _ => self.int_lit(ty),
            },
            1 => {
                let a = self.int_expr(vars, ty, depth - 1);
                let b = self.int_expr(vars, ty, depth - 1);
                let m = ["wrapping_add", "wrapping_sub", "wrapping_mul"]
                    [self.rng.random_range(0..3)];
                format!("({a}).{m}({b})")
            }
            2 => {
                let a = self.int_expr(vars, ty, depth - 1);
                let b = self.int_expr(vars, ty, depth - 1);
                let op = ["+", "-", "*"][self.rng.random_range(0..3)];
                format!("({a} {op} {b})")
            }
            3 => {
                let a = self.int_expr(vars, ty, depth - 1);
                let b = self.int_expr(vars, ty, depth - 1);
                let c = self.bool_expr(vars, ty, depth - 1);
                format!("(if {c} {{ {a} }} else {{ {b} }})")
            }
            4 => {
                // bitwise op (always total)
                let a = self.int_expr(vars, ty, depth - 1);
                let b = self.int_expr(vars, ty, depth - 1);
                let op = ["|", "&", "^"][self.rng.random_range(0..3)];
                format!("({a} {op} {b})")
            }
            _ => {
                // unsigned-only guarded division (divisor forced nonzero).
                let a = self.int_expr(vars, ty, depth - 1);
                let b = self.int_expr(vars, ty, depth - 1);
                format!("({a} / (({b}) | 1))")
            }
        }
    }

    /// A boolean expression over the in-scope int `vars`.
    fn bool_expr(&mut self, vars: &[String], ty: &str, depth: usize) -> String {
        if depth == 0 {
            let a = self.int_expr(vars, ty, 1);
            let b = self.int_expr(vars, ty, 1);
            let cmp = ["<", "<=", ">", ">=", "==", "!="][self.rng.random_range(0..6)];
            return format!("({a} {cmp} {b})");
        }
        // NB: no bare `true`/`false` arm. A constant-bool `assert!(true)` /
        // `assert!(false)` crashes the fork aeneas at InterpExpressions.ml:55
        // (the N1 assert-operand double-eval family) — which both poisons the
        // semdiff batch and is worthless for a semantic differential. Every
        // boolean is a non-trivial comparison / connective.
        match self.rng.random_range(0..4) {
            0 | 1 => {
                let a = self.int_expr(vars, ty, depth);
                let b = self.int_expr(vars, ty, depth);
                let cmp = ["<", "<=", ">", ">=", "==", "!="][self.rng.random_range(0..6)];
                format!("({a} {cmp} {b})")
            }
            2 => {
                let a = self.bool_expr(vars, ty, depth - 1);
                let b = self.bool_expr(vars, ty, depth - 1);
                let op = if self.rng.random_bool(0.5) { "&&" } else { "||" };
                format!("({a} {op} {b})")
            }
            _ => {
                let a = self.bool_expr(vars, ty, depth - 1);
                format!("(!{a})")
            }
        }
    }

    /// A small `while i < BOUND` iteration bound (u32).
    fn loop_bound(&mut self) -> u32 {
        self.rng.random_range(2..=8)
    }

    // -- open shapes --------------------------------------------------------

    /// Generate one open (borrow-parameter) function `gen_open_<idx>`, weighted
    /// toward the borrow-heavy families.
    fn open_fn(&mut self, idx: usize) -> OpenFn {
        // (shape-id, weight)
        const W: &[(u32, u32)] = &[
            (0, 5), // loop_return_borrow  (F4 family)
            (1, 5), // shared_reassign_loop (F6 family)
            (2, 4), // mut_return_reborrow
            (3, 4), // mut_return_field (branch-join borrow)
            (4, 4), // enum_borrow_match
            (5, 3), // struct_borrow
            (6, 3), // two_phase_method
            (7, 3), // break_with_value (F4 family)
            (8, 3), // array_mut_loop
            (9, 2), // nested_match (value-only joins)
            (10, 1), // arith_chain (value-only)
        ];
        let shape = weighted_pick(&mut self.rng, W);
        let ty = self.int_ty();
        let name = format!("gen_open_{idx}");
        match shape {
            0 => self.open_loop_return_borrow(&name, ty),
            1 => self.open_shared_reassign_loop(&name, ty),
            2 => self.open_mut_return_reborrow(&name, ty),
            3 => self.open_mut_return_field(&name, ty, idx),
            4 => self.open_enum_borrow_match(&name, ty, idx),
            5 => self.open_struct_borrow(&name, ty, idx),
            6 => self.open_two_phase_method(&name, ty, idx),
            7 => self.open_break_with_value(&name, ty),
            8 => self.open_array_mut_loop(&name, ty),
            9 => self.open_nested_match(&name, ty),
            _ => self.open_arith_chain(&name, ty),
        }
    }

    fn open_loop_return_borrow(&mut self, name: &str, ty: &str) -> OpenFn {
        let bound = self.rng.random_range(3..=20);
        let step = self.int_expr(&["*x".to_string()], ty, 1);
        let func = format!(
            "fn {name}(x: &mut {ty}) -> {ty} {{\n    let mut i: u32 = 0;\n    loop {{\n        if *x > {bound} {{ return *x; }}\n        *x = ({step}).wrapping_add(1);\n        i = i.wrapping_add(1);\n        if i > 1000 {{ return *x; }}\n    }}\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_shared_reassign_loop(&mut self, name: &str, ty: &str) -> OpenFn {
        let bound = self.loop_bound();
        let acc = self.int_expr(&["s".to_string(), "(*x)".to_string()], ty, 2);
        let func = format!(
            "fn {name}<'a>(mut x: &'a {ty}, y: &'a {ty}) -> {ty} {{\n    let mut s: {ty} = *x;\n    x = y;\n    let mut i: u32 = 0;\n    while i < {bound} {{\n        s = ({acc}).wrapping_add(*x);\n        i = i.wrapping_add(1);\n    }}\n    s\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_mut_return_reborrow(&mut self, name: &str, ty: &str) -> OpenFn {
        let lit = self.int_lit(ty);
        // A reborrow chain of depth 1 or 2.
        let chain = if self.rng.random_bool(0.5) {
            "let y = &mut *x;\n    let z = &mut *y;\n    z"
        } else {
            "let y = &mut *x;\n    y"
        };
        let func = format!(
            "fn {name}(x: &mut {ty}) -> &mut {ty} {{\n    *x = (*x).wrapping_add({lit});\n    {chain}\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_mut_return_field(&mut self, name: &str, ty: &str, idx: usize) -> OpenFn {
        let s = format!("Gs{idx}");
        let support = vec![format!("struct {s} {{ a: {ty}, b: {ty} }}")];
        let func = format!(
            "fn {name}(s: &mut {s}) -> &mut {ty} {{\n    if s.a > s.b {{ &mut s.a }} else {{ &mut s.b }}\n}}"
        );
        OpenFn { support, func }
    }

    fn open_enum_borrow_match(&mut self, name: &str, ty: &str, idx: usize) -> OpenFn {
        let e = format!("Ge{idx}");
        let support = vec![format!("enum {e}<'a> {{ A(&'a {ty}), B(&'a mut {ty}) }}")];
        let func = format!(
            "fn {name}<'a>(e: {e}<'a>) -> {ty} {{\n    match e {{\n        {e}::A(r) => *r,\n        {e}::B(r) => {{ *r = (*r).wrapping_add(1); *r }}\n    }}\n}}"
        );
        OpenFn { support, func }
    }

    fn open_struct_borrow(&mut self, name: &str, ty: &str, idx: usize) -> OpenFn {
        let w = format!("Gw{idx}");
        let lit = self.int_lit(ty);
        let support = vec![format!("struct {w}<'a> {{ r: &'a mut {ty} }}")];
        let func = format!(
            "fn {name}(w: {w}<'_>) -> {ty} {{\n    *w.r = (*w.r).wrapping_add({lit});\n    *w.r\n}}"
        );
        OpenFn { support, func }
    }

    fn open_two_phase_method(&mut self, name: &str, ty: &str, idx: usize) -> OpenFn {
        let c = format!("Gc{idx}");
        let support = vec![format!(
            "struct {c} {{ f0: {ty} }}\nimpl {c} {{\n    fn bump(&mut self, k: {ty}) {{ self.f0 = self.f0.wrapping_add(k); }}\n    fn get(&self) -> {ty} {{ self.f0 }}\n}}"
        )];
        let func = format!(
            "fn {name}(c: &mut {c}) -> {ty} {{\n    c.bump(c.get());\n    c.get()\n}}"
        );
        OpenFn { support, func }
    }

    fn open_break_with_value(&mut self, name: &str, ty: &str) -> OpenFn {
        let bound = self.rng.random_range(3..=20);
        let func = format!(
            "fn {name}(x: &mut {ty}) -> {ty} {{\n    let r = loop {{\n        *x = (*x).wrapping_add(1);\n        if *x > {bound} {{ break *x; }}\n    }};\n    r\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_array_mut_loop(&mut self, name: &str, ty: &str) -> OpenFn {
        let acc = self.int_expr(&["s".to_string()], ty, 1);
        let func = format!(
            "fn {name}(a: &mut [{ty}; 4]) -> {ty} {{\n    let mut s: {ty} = 0;\n    let mut i: usize = 0;\n    while i < 4 {{\n        a[i] = a[i].wrapping_add(1);\n        s = ({acc}).wrapping_add(a[i]);\n        i = i.wrapping_add(1);\n    }}\n    s\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_nested_match(&mut self, name: &str, ty: &str) -> OpenFn {
        let env = vec!["a".to_string(), "b".to_string()];
        let e1 = self.int_expr(&env, ty, 2);
        let e2 = self.int_expr(&env, ty, 2);
        let e3 = self.int_expr(&env, ty, 2);
        let e4 = self.int_expr(&env, ty, 2);
        let func = format!(
            "fn {name}(a: {ty}, b: {ty}, c: bool) -> {ty} {{\n    match (a > b, c) {{\n        (true, true) => {e1},\n        (true, false) => {e2},\n        (false, true) => {e3},\n        (false, false) => {e4},\n    }}\n}}"
        );
        OpenFn { support: vec![], func }
    }

    fn open_arith_chain(&mut self, name: &str, ty: &str) -> OpenFn {
        let mut env = vec!["a".to_string(), "b".to_string()];
        let e1 = self.int_expr(&env, ty, 2);
        env.push("c".to_string());
        let e2 = self.int_expr(&env, ty, 2);
        env.push("d".to_string());
        let e3 = self.int_expr(&env, ty, 2);
        let func = format!(
            "fn {name}(a: {ty}, b: {ty}) -> {ty} {{\n    let c = {e1};\n    let d = {e2};\n    {e3}\n}}"
        );
        OpenFn { support: vec![], func }
    }

    // -- closed shapes ------------------------------------------------------

    /// Generate one closed niladic `test_<idx>` function, weighted toward the
    /// same borrow-heavy families expressed over local borrows, always bounded
    /// (terminating) and ending in `assert!`s.
    fn closed_fn(&mut self, idx: usize) -> ClosedFn {
        // NB: no char-match shape. Matching a *concrete* `char` literal crashes
        // the fork aeneas with `[Error] Inconsistent state`
        // (interp/InterpStatements.ml:1100 — the concrete-eval path, a cousin of
        // the N1 assert double-eval), and a char *range* pattern (`'a'..='m'`)
        // lowers to noncomputable `Step` axioms → LEAN_INCONCLUSIVE. Both are
        // pure noise for the semantic differential, so `char` is exercised only
        // where it evaluates cleanly (it is not currently generated for the
        // closed oracle — see the coverage notes).
        const W: &[(u32, u32)] = &[
            (0, 5), // loop_borrow (F4 family)
            (1, 5), // shared_reassign (F6 family)
            (2, 4), // array_loop
            (3, 4), // enum_borrow_match
            (4, 3), // struct_two_phase
            (5, 3), // break_with_value (F4 family)
            (6, 3), // nested_match
            (7, 3), // arith_chain
        ];
        let shape = weighted_pick(&mut self.rng, W);
        let ty = self.int_ty();
        let name = format!("test_{idx}");
        let (support, body) = match shape {
            0 => (vec![], self.closed_loop_borrow(ty)),
            1 => (vec![], self.closed_shared_reassign(ty)),
            2 => (vec![], self.closed_array_loop(ty)),
            3 => self.closed_enum_borrow(ty, idx),
            4 => self.closed_struct_two_phase(ty, idx),
            5 => (vec![], self.closed_break_with_value(ty)),
            6 => (vec![], self.closed_nested_match(ty)),
            _ => (vec![], self.closed_arith_chain(ty)),
        };
        let func = format!("pub fn {name}() {{\n{body}}}");
        ClosedFn { name, support, func }
    }

    fn assert_line(&mut self, env: &[String], ty: &str) -> String {
        let b = self.bool_expr(env, ty, 1);
        format!("    assert!({b});\n")
    }

    fn closed_loop_borrow(&mut self, ty: &str) -> String {
        let init = self.int_lit(ty);
        let bound = self.rng.random_range(3..=15);
        let env = vec!["base".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let mut base: {ty} = {init};\n"));
        s.push_str("    let x = &mut base;\n");
        s.push_str("    let mut i: u32 = 0;\n");
        s.push_str("    loop {\n");
        s.push_str(&format!("        if *x > {bound} {{ break; }}\n"));
        s.push_str("        *x = (*x).wrapping_add(1);\n");
        s.push_str("        i = i.wrapping_add(1);\n");
        s.push_str("        if i > 100 { break; }\n");
        s.push_str("    }\n");
        s.push_str(&self.assert_line(&env, ty));
        s
    }

    fn closed_shared_reassign(&mut self, ty: &str) -> String {
        let p = self.int_lit(ty);
        let q = self.int_lit(ty);
        let bound = self.loop_bound();
        let acc = self.int_expr(&["s".to_string()], ty, 1);
        let env = vec!["s".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let p: {ty} = {p};\n"));
        s.push_str(&format!("    let q: {ty} = {q};\n"));
        s.push_str("    let mut x: &_ = &p;\n");
        s.push_str(&format!("    let mut s: {ty} = *x;\n"));
        s.push_str("    x = &q;\n");
        s.push_str("    let mut i: u32 = 0;\n");
        s.push_str(&format!("    while i < {bound} {{\n"));
        s.push_str(&format!("        s = ({acc}).wrapping_add(*x);\n"));
        s.push_str("        i = i.wrapping_add(1);\n");
        s.push_str("    }\n");
        s.push_str(&self.assert_line(&env, ty));
        s
    }

    fn closed_array_loop(&mut self, ty: &str) -> String {
        let l0 = self.int_lit(ty);
        let l1 = self.int_lit(ty);
        let l2 = self.int_lit(ty);
        let l3 = self.int_lit(ty);
        let env = vec!["s".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let mut a: [{ty}; 4] = [{l0}, {l1}, {l2}, {l3}];\n"));
        s.push_str("    let r = &mut a;\n");
        s.push_str("    let mut i: usize = 0;\n");
        s.push_str(&format!("    let mut s: {ty} = 0;\n"));
        s.push_str("    while i < 4 {\n");
        s.push_str("        r[i] = r[i].wrapping_add(1);\n");
        s.push_str("        s = s.wrapping_add(r[i]);\n");
        s.push_str("        i = i.wrapping_add(1);\n");
        s.push_str("    }\n");
        s.push_str(&self.assert_line(&env, ty));
        s
    }

    fn closed_enum_borrow(&mut self, ty: &str, idx: usize) -> (Vec<String>, String) {
        let e = format!("Ge{idx}");
        let support = vec![format!("enum {e}<'a> {{ A(&'a {ty}), B(&'a mut {ty}) }}")];
        let init = self.int_lit(ty);
        let use_b = self.rng.random_bool(0.5);
        let env = vec!["v".to_string(), "base".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let mut base: {ty} = {init};\n"));
        if use_b {
            s.push_str(&format!("    let e = {e}::B(&mut base);\n"));
        } else {
            s.push_str(&format!("    let e = {e}::A(&base);\n"));
        }
        s.push_str(&format!(
            "    let v: {ty} = match e {{ {e}::A(r) => *r, {e}::B(r) => {{ *r = (*r).wrapping_add(1); *r }} }};\n"
        ));
        s.push_str(&self.assert_line(&env, ty));
        (support, s)
    }

    fn closed_struct_two_phase(&mut self, ty: &str, idx: usize) -> (Vec<String>, String) {
        let c = format!("Gc{idx}");
        let support = vec![format!(
            "struct {c} {{ f0: {ty} }}\nimpl {c} {{\n    fn bump(&mut self, k: {ty}) {{ self.f0 = self.f0.wrapping_add(k); }}\n    fn get(&self) -> {ty} {{ self.f0 }}\n}}"
        )];
        let init = self.int_lit(ty);
        let env = vec!["out".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let mut c = {c} {{ f0: {init} }};\n"));
        s.push_str("    c.bump(c.get());\n");
        s.push_str(&format!("    let out: {ty} = c.get();\n"));
        s.push_str(&self.assert_line(&env, ty));
        (support, s)
    }

    fn closed_break_with_value(&mut self, ty: &str) -> String {
        let init = self.int_lit(ty);
        let bound = self.rng.random_range(3..=15);
        let env = vec!["r".to_string(), "base".to_string()];
        let mut s = String::new();
        s.push_str(&format!("    let mut base: {ty} = {init};\n"));
        s.push_str("    let x = &mut base;\n");
        s.push_str("    let mut i: u32 = 0;\n");
        s.push_str(&format!("    let r: {ty} = loop {{\n"));
        s.push_str("        *x = (*x).wrapping_add(1);\n");
        s.push_str("        i = i.wrapping_add(1);\n");
        s.push_str(&format!("        if *x > {bound} || i > 100 {{ break *x; }}\n"));
        s.push_str("    };\n");
        s.push_str(&self.assert_line(&env, ty));
        s
    }

    fn closed_nested_match(&mut self, ty: &str) -> String {
        let a = self.int_lit(ty);
        let b = self.int_lit(ty);
        let env = vec!["a".to_string(), "b".to_string()];
        let e1 = self.int_expr(&env, ty, 2);
        let e2 = self.int_expr(&env, ty, 2);
        let e3 = self.int_expr(&env, ty, 2);
        let e4 = self.int_expr(&env, ty, 2);
        let cond = self.bool_expr(&env, ty, 1);
        let mut s = String::new();
        s.push_str(&format!("    let a: {ty} = {a};\n"));
        s.push_str(&format!("    let b: {ty} = {b};\n"));
        s.push_str(&format!("    let c: bool = {cond};\n"));
        s.push_str(&format!(
            "    let out: {ty} = match (a > b, c) {{ (true, true) => {e1}, (true, false) => {e2}, (false, true) => {e3}, (false, false) => {e4} }};\n"
        ));
        let env2 = vec!["a".to_string(), "b".to_string(), "out".to_string()];
        s.push_str(&self.assert_line(&env2, ty));
        s
    }

    fn closed_arith_chain(&mut self, ty: &str) -> String {
        let n = self.rng.random_range(2..=4);
        let mut env: Vec<String> = Vec::new();
        let mut s = String::new();
        for k in 0..n {
            let e = self.int_expr(&env, ty, 2);
            let v = format!("v{k}");
            s.push_str(&format!("    let mut {v}: {ty} = {e};\n"));
            env.push(v);
        }
        s.push_str(&self.assert_line(&env, ty));
        s
    }
}

/// Weighted choice over `(item, weight)` pairs.
fn weighted_pick(rng: &mut ChaCha8Rng, choices: &[(u32, u32)]) -> u32 {
    let total: u32 = choices.iter().map(|(_, w)| *w).sum();
    let mut r = rng.random_range(0..total);
    for (item, w) in choices {
        if r < *w {
            return *item;
        }
        r -= *w;
    }
    choices[0].0
}

/// Render a self-contained mini-crate (allow-header + support items + fn body).
fn render_mini(support: &[String], func: &str) -> String {
    let mut s = String::new();
    s.push_str(GEN_HEADER);
    for it in support {
        s.push_str(it);
        s.push_str("\n\n");
    }
    s.push_str(func);
    s.push('\n');
    s
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Generate `count` open (borrow-parameter) functions as corpus [`Unit`]s,
/// deterministic in `(seed, index)`. Each function is parsed (with its support
/// items) via the corpus extractor so it flows through the existing pack /
/// pipeline / oracle path unchanged. Units that fail to parse are skipped (the
/// rustc gate would drop them anyway); the returned count may be `< count`.
pub fn gen_open_units(seed: u64, count: usize) -> Vec<Unit> {
    let mut g = Gen::new(seed);
    let mut out = Vec::new();
    let seed_file = format!("gen://open/seed{seed}");
    for idx in 0..count {
        let of = g.open_fn(idx);
        let src = render_mini(&of.support, &of.func);
        match corpus::units_from_source(&src, Path::new(&seed_file)) {
            Ok(units) => out.extend(units),
            Err(_) => continue,
        }
    }
    out
}

/// Generate one open mini-crate source (for the `gen` subcommand / yield check).
pub fn gen_open_source(seed: u64, idx: usize) -> String {
    let mut g = Gen::new(seed.wrapping_add(idx as u64));
    let of = g.open_fn(idx);
    render_mini(&of.support, &of.func)
}

/// A generated closed crate: the full source plus the list of `test_*` names.
pub struct ClosedCrate {
    pub source: String,
    pub test_names: Vec<String>,
}

/// Generate a closed deterministic test crate with `count` niladic `test_*`
/// functions for the semantic differential. Support items are uniquely named
/// per function index (no collisions). Deterministic in `(seed, count)`.
pub fn gen_closed_crate(seed: u64, count: usize) -> ClosedCrate {
    let mut g = Gen::new(seed);
    let mut support: Vec<String> = Vec::new();
    let mut funcs: Vec<String> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    for idx in 0..count {
        let cf = g.closed_fn(idx);
        for it in cf.support {
            if !support.contains(&it) {
                support.push(it);
            }
        }
        funcs.push(cf.func);
        names.push(cf.name);
    }
    let mut src = String::new();
    src.push_str(GEN_HEADER);
    src.push_str("// AUTO-GENERATED closed semdiff crate. Do not edit.\n\n");
    for it in &support {
        src.push_str(it);
        src.push_str("\n\n");
    }
    for f in &funcs {
        src.push_str(f);
        src.push_str("\n\n");
    }
    ClosedCrate {
        source: src,
        test_names: names,
    }
}

/// Run rustc as a validity gate on a standalone source string (edition 2021,
/// rlib, metadata-only). Returns true iff rustc accepts it (warnings ok). Used
/// to measure generator yield.
pub fn rustc_accepts(source: &str) -> bool {
    let dir = std::env::temp_dir().join(format!(
        "aeneas-fuzz-gen-{}-{}",
        std::process::id(),
        fast_rand_tag()
    ));
    if std::fs::create_dir_all(&dir).is_err() {
        return false;
    }
    let src_path = dir.join("gen.rs");
    let meta_path = dir.join("gen.rmeta");
    let ok = std::fs::write(&src_path, source).is_ok()
        && Command::new("rustc")
            .args([
                "--edition=2021",
                "--crate-type=rlib",
                "--emit=metadata",
                "-o",
            ])
            .arg(&meta_path)
            .arg(&src_path)
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);
    let _ = std::fs::remove_dir_all(&dir);
    ok
}

/// A cheap unique-ish tag for temp dir names (avoids adding a rand dep here).
fn fast_rand_tag() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0)
}

/// The measured yield of a batch: `accepted / generated`.
#[derive(Debug, Clone, Copy)]
pub struct Yield {
    pub generated: usize,
    pub accepted: usize,
}

impl Yield {
    pub fn fraction(&self) -> f64 {
        if self.generated == 0 {
            0.0
        } else {
            self.accepted as f64 / self.generated as f64
        }
    }
}

/// Measure the rustc-yield of `count` open functions from `seed` by checking
/// each mini-crate individually.
pub fn measure_open_yield(seed: u64, count: usize) -> Yield {
    let mut g = Gen::new(seed);
    let mut accepted = 0;
    for idx in 0..count {
        let of = g.open_fn(idx);
        let src = render_mini(&of.support, &of.func);
        if rustc_accepts(&src) {
            accepted += 1;
        }
    }
    Yield {
        generated: count,
        accepted,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every generated open function must parse as valid Rust.
    #[test]
    fn open_functions_parse() {
        for idx in 0..200 {
            let src = gen_open_source(1234, idx);
            syn::parse_file(&src)
                .unwrap_or_else(|e| panic!("open gen {idx} did not parse: {e}\n{src}"));
        }
    }

    /// The closed crate must parse and expose the promised `test_*` names.
    #[test]
    fn closed_crate_parses_and_lists_tests() {
        let crate_ = gen_closed_crate(42, 60);
        syn::parse_file(&crate_.source)
            .unwrap_or_else(|e| panic!("closed crate did not parse: {e}\n{}", crate_.source));
        assert_eq!(crate_.test_names.len(), 60);
        for (i, n) in crate_.test_names.iter().enumerate() {
            assert_eq!(n, &format!("test_{i}"));
            assert!(crate_.source.contains(&format!("pub fn {n}()")));
        }
    }

    /// Generation is deterministic in the seed.
    #[test]
    fn generation_is_deterministic() {
        let a = gen_closed_crate(7, 40).source;
        let b = gen_closed_crate(7, 40).source;
        assert_eq!(a, b);
        let c = gen_closed_crate(8, 40).source;
        assert_ne!(a, c, "different seeds should differ");
    }

    /// gen_open_units yields borrow-parameter units the corpus can extract.
    #[test]
    fn open_units_extractable() {
        let units = gen_open_units(99, 40);
        assert!(units.len() >= 30, "expected most units to extract, got {}", units.len());
        // At least some carry a borrow in the signature (borrow-heavy weighting).
        let borrow_sigs = units
            .iter()
            .filter(|u| {
                use quote::ToTokens;
                let sig = u.func.sig.to_token_stream().to_string();
                sig.contains('&')
            })
            .count();
        assert!(borrow_sigs > 0, "expected borrow-bearing signatures");
    }

    /// rustc-yield on a fixed seed must clear the >70% bar (Part A requirement).
    /// Gated on rustc being available; skips cleanly otherwise.
    #[test]
    fn open_yield_is_high() {
        if Command::new("rustc").arg("--version").output().is_err() {
            eprintln!("[gen test] rustc unavailable; skipping yield test");
            return;
        }
        let y = measure_open_yield(2024, 60);
        assert!(
            y.fraction() > 0.70,
            "open rustc-yield too low: {}/{} = {:.2}",
            y.accepted,
            y.generated,
            y.fraction()
        );
    }

    /// The closed crate must also rustc-gate cleanly (it is stable Rust: no
    /// nightly attrs, no range-for).
    #[test]
    fn closed_crate_rustc_gates() {
        if Command::new("rustc").arg("--version").output().is_err() {
            eprintln!("[gen test] rustc unavailable; skipping closed gate test");
            return;
        }
        let crate_ = gen_closed_crate(2025, 60);
        assert!(
            rustc_accepts(&crate_.source),
            "closed crate failed rustc gate:\n{}",
            crate_.source
        );
        // And it must not contain a range-for (would be Lean-inconclusive).
        assert!(!crate_.source.contains(" in "), "closed crate must avoid for-in loops");
    }
}
