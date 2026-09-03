//! Seed corpus loading, function extraction, and packing.
//!
//! We load `.rs` seed files, parse them with `syn`, and extract *units*: a free
//! function together with the transitive closure of the file-local items it
//! needs (types, consts, impls, helper fns, `use`s). Packing bundles N units
//! into one crate (`lib.rs`), renaming each primary function to
//! `f_<i>_<origname>` and emitting a deduped prelude of shared support items.
//!
//! Extraction is best-effort: it carries what it can resolve locally and leaves
//! everything else to the rustc validity gate (which drops non-compiling units).

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use syn::visit::Visit;
use syn::{Item, ItemFn};

/// Where a packed function came from and how it was transformed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Provenance {
    pub orig_name: String,
    pub seed_file: String,
    /// Ordered mutation-chain (mutator variant names).
    #[serde(default)]
    pub mutations: Vec<String>,
}

impl Provenance {
    pub fn seed(orig_name: &str, seed_file: &str) -> Provenance {
        Provenance {
            orig_name: orig_name.to_string(),
            seed_file: seed_file.to_string(),
            mutations: Vec::new(),
        }
    }
}

/// A rendered, dedup-keyed support item carried alongside a function.
#[derive(Clone, Debug)]
pub struct Carried {
    /// Dedup key, e.g. `type:Foo`, `fn:helper`, `const:C`, `impl:Foo`, `use:...`.
    pub key: String,
    /// Rendered source text (visibility normalized to `pub` where applicable).
    pub text: String,
}

/// A single extractable unit: one primary function + its support closure.
#[derive(Clone)]
pub struct Unit {
    pub orig_name: String,
    pub seed_file: PathBuf,
    /// The primary function (mutable target for mutators).
    pub func: ItemFn,
    /// Deduped support items required to compile `func`.
    pub support: Vec<Carried>,
}

impl Unit {
    pub fn provenance(&self) -> Provenance {
        Provenance::seed(&self.orig_name, &self.seed_file.to_string_lossy())
    }
}

/// A loaded corpus: a pool of independently-packable units.
pub struct Corpus {
    pub units: Vec<Unit>,
}

impl Corpus {
    pub fn len(&self) -> usize {
        self.units.len()
    }
    pub fn is_empty(&self) -> bool {
        self.units.is_empty()
    }

    /// Build a corpus directly from already-extracted units (e.g. the grammar
    /// generator's output). Order is preserved.
    pub fn from_units(units: Vec<Unit>) -> Corpus {
        Corpus { units }
    }

    /// Load and extract units from every `.rs` file under the given dirs
    /// (recursively). Files that fail to parse are skipped with a warning.
    pub fn load(dirs: &[PathBuf]) -> Result<Corpus> {
        let mut files = Vec::new();
        for d in dirs {
            collect_rs_files(d, &mut files)?;
        }
        files.sort();
        let mut units = Vec::new();
        for f in files {
            match extract_units_from_file(&f) {
                Ok(mut us) => units.append(&mut us),
                Err(e) => eprintln!("[corpus] skip {}: {}", f.display(), e),
            }
        }
        // Deterministic order.
        units.sort_by(|a, b| {
            (a.seed_file.clone(), a.orig_name.clone())
                .cmp(&(b.seed_file.clone(), b.orig_name.clone()))
        });
        Ok(Corpus { units })
    }
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    if dir.is_file() {
        if dir.extension().map(|e| e == "rs").unwrap_or(false) {
            out.push(dir.to_path_buf());
        }
        return Ok(());
    }
    if !dir.is_dir() {
        return Ok(());
    }
    for entry in std::fs::read_dir(dir).with_context(|| format!("reading dir {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out)?;
        } else if path.extension().map(|e| e == "rs").unwrap_or(false) {
            out.push(path);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Ident collection
// ---------------------------------------------------------------------------

/// Collects the leading path segment of every type/expr/macro path reference,
/// so we can resolve which file-local items a function depends on.
#[derive(Default)]
struct IdentCollector {
    names: BTreeSet<String>,
    saw_crate_or_super: bool,
}

impl<'ast> Visit<'ast> for IdentCollector {
    fn visit_path(&mut self, p: &'ast syn::Path) {
        if let Some(first) = p.segments.first() {
            let s = first.ident.to_string();
            if s == "crate" || s == "super" {
                self.saw_crate_or_super = true;
            }
            self.names.insert(s);
            // also record the last segment (e.g. `Foo` in `mod::Foo`)
            if let Some(last) = p.segments.last() {
                self.names.insert(last.ident.to_string());
            }
        }
        syn::visit::visit_path(self, p);
    }

    fn visit_ident(&mut self, id: &'ast proc_macro2::Ident) {
        self.names.insert(id.to_string());
    }
}

fn collect_idents_fn(f: &ItemFn) -> IdentCollector {
    let mut c = IdentCollector::default();
    c.visit_item_fn(f);
    c
}

fn collect_idents_item(item: &Item) -> IdentCollector {
    let mut c = IdentCollector::default();
    c.visit_item(item);
    c
}

/// Generic type-parameter names declared by a function/item, which must NOT be
/// treated as file-local type dependencies.
fn fn_generic_params(f: &ItemFn) -> BTreeSet<String> {
    generics_params(&f.sig.generics)
}

fn generics_params(g: &syn::Generics) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for p in &g.params {
        if let syn::GenericParam::Type(t) = p {
            out.insert(t.ident.to_string());
        }
    }
    out
}

// ---------------------------------------------------------------------------
// File-level pools
// ---------------------------------------------------------------------------

struct FilePools {
    types: BTreeMap<String, Item>,   // struct/enum/union/type-alias/trait
    consts: BTreeMap<String, Item>,  // const/static
    fns: BTreeMap<String, ItemFn>,   // free functions
    impls: Vec<syn::ItemImpl>,       // inherent + trait impls
    uses: Vec<syn::ItemUse>,
}

fn self_type_name(imp: &syn::ItemImpl) -> Option<String> {
    if let syn::Type::Path(tp) = &*imp.self_ty {
        tp.path.segments.last().map(|s| s.ident.to_string())
    } else {
        None
    }
}

fn impl_trait_name(imp: &syn::ItemImpl) -> Option<String> {
    imp.trait_
        .as_ref()
        .and_then(|(_, path, _)| path.segments.last().map(|s| s.ident.to_string()))
}

fn build_pools(file: &syn::File) -> FilePools {
    let mut pools = FilePools {
        types: BTreeMap::new(),
        consts: BTreeMap::new(),
        fns: BTreeMap::new(),
        impls: Vec::new(),
        uses: Vec::new(),
    };
    for item in &file.items {
        match item {
            Item::Struct(s) => {
                pools.types.insert(s.ident.to_string(), item.clone());
            }
            Item::Enum(e) => {
                pools.types.insert(e.ident.to_string(), item.clone());
            }
            Item::Union(u) => {
                pools.types.insert(u.ident.to_string(), item.clone());
            }
            Item::Type(t) => {
                pools.types.insert(t.ident.to_string(), item.clone());
            }
            Item::Trait(t) => {
                pools.types.insert(t.ident.to_string(), item.clone());
            }
            Item::Const(c) => {
                pools.consts.insert(c.ident.to_string(), item.clone());
            }
            Item::Static(s) => {
                pools.consts.insert(s.ident.to_string(), item.clone());
            }
            Item::Fn(f) => {
                pools.fns.insert(f.sig.ident.to_string(), f.clone());
            }
            Item::Impl(i) => pools.impls.push(i.clone()),
            Item::Use(u) => pools.uses.push(u.clone()),
            _ => {}
        }
    }
    pools
}

// ---------------------------------------------------------------------------
// Rendering (visibility normalization + pretty printing)
// ---------------------------------------------------------------------------

fn make_pub(vis: &mut syn::Visibility) {
    *vis = syn::Visibility::Public(syn::token::Pub::default());
}

/// Render an item to formatted Rust, forcing top-level `pub` where it has a
/// visibility (so `pub` primary fns don't leak private types: E0446).
fn render_item_pub(item: &Item) -> String {
    let mut item = item.clone();
    match &mut item {
        Item::Struct(s) => make_pub(&mut s.vis),
        Item::Enum(e) => make_pub(&mut e.vis),
        Item::Union(u) => make_pub(&mut u.vis),
        Item::Type(t) => make_pub(&mut t.vis),
        Item::Trait(t) => make_pub(&mut t.vis),
        Item::Const(c) => make_pub(&mut c.vis),
        Item::Static(s) => make_pub(&mut s.vis),
        Item::Fn(f) => make_pub(&mut f.vis),
        _ => {}
    }
    render_item(&item)
}

fn render_item(item: &Item) -> String {
    let file = syn::File {
        shebang: None,
        attrs: vec![],
        items: vec![item.clone()],
    };
    prettyplease::unparse(&file)
}

/// Render a free function as a packed `pub fn f_<i>_<name>` with a new name.
pub fn render_primary(f: &ItemFn, final_name: &str) -> String {
    let mut f = f.clone();
    make_pub(&mut f.vis);
    f.sig.ident = syn::Ident::new(final_name, f.sig.ident.span());
    render_item(&Item::Fn(f))
}

// ---------------------------------------------------------------------------
// Unit extraction
// ---------------------------------------------------------------------------

fn extract_units_from_file(path: &Path) -> Result<Vec<Unit>> {
    let text = std::fs::read_to_string(path)?;
    let file: syn::File = syn::parse_file(&text)
        .with_context(|| format!("syn parse failed for {}", path.display()))?;
    let pools = build_pools(&file);

    // Rendered `use` items (shared across all units from this file), each paired
    // with its root path segment so we can drop file-local imports a unit does
    // not actually pull in (see `extract_one_unit`).
    let use_items = build_use_items(&pools);

    let mut units = Vec::new();
    for (name, f) in &pools.fns {
        match extract_one_unit(f, &pools, &use_items) {
            Some(unit) => units.push(unit),
            None => {
                // could not resolve; skip this function
                let _ = name;
            }
        }
    }
    // annotate seed_file
    for u in &mut units {
        u.seed_file = path.to_path_buf();
    }
    Ok(units)
}

/// The root (leading) path segment of a `use` tree, e.g. `List` in
/// `use List::Cons;` or `std` in `use std::vec::Vec;`.
fn use_root(u: &syn::ItemUse) -> Option<String> {
    match &u.tree {
        syn::UseTree::Path(p) => Some(p.ident.to_string()),
        syn::UseTree::Name(n) => Some(n.ident.to_string()),
        syn::UseTree::Rename(r) => Some(r.ident.to_string()),
        _ => None,
    }
}

/// Render the file's non-glob `use` items, each paired with its root segment.
fn build_use_items(pools: &FilePools) -> Vec<(Option<String>, Carried)> {
    pools
        .uses
        .iter()
        .filter(|u| !is_glob_use(u))
        .map(|u| {
            let text = render_item(&Item::Use(u.clone()));
            let carried = Carried {
                key: format!("use:{}", text.trim()),
                text: text.trim_end().to_string(),
            };
            (use_root(u), carried)
        })
        .collect()
}

fn is_glob_use(u: &syn::ItemUse) -> bool {
    fn tree_has_glob(t: &syn::UseTree) -> bool {
        match t {
            syn::UseTree::Glob(_) => true,
            syn::UseTree::Group(g) => g.items.iter().any(tree_has_glob),
            syn::UseTree::Path(p) => tree_has_glob(&p.tree),
            _ => false,
        }
    }
    tree_has_glob(&u.tree)
}

/// Build a single unit for `f`, carrying the transitive local support closure.
/// Returns None if the function references `crate::`/`super::` (unresolvable
/// after repackaging).
fn extract_one_unit(
    f: &ItemFn,
    pools: &FilePools,
    uses: &[(Option<String>, Carried)],
) -> Option<Unit> {
    let idents = collect_idents_fn(f);
    if idents.saw_crate_or_super {
        return None;
    }

    let mut support: Vec<Carried> = Vec::new();
    let mut seen_keys: BTreeSet<String> = BTreeSet::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();

    // Seed the worklist with the function's referenced names, minus its own
    // generic params.
    let generics = fn_generic_params(f);
    let mut work: Vec<String> = idents
        .names
        .iter()
        .filter(|n| !generics.contains(*n))
        .cloned()
        .collect();

    let self_name = f.sig.ident.to_string();

    while let Some(name) = work.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if name == self_name {
            continue;
        }

        if let Some(item) = pools.types.get(&name) {
            push_carried(
                &mut support,
                &mut seen_keys,
                format!("type:{}", name),
                render_item_pub(item),
            );
            // recurse into the type's own references, minus its generic params.
            let inner = collect_idents_item(item);
            let inner_generics = item_generics(item);
            for n in inner.names {
                if !inner_generics.contains(&n) {
                    work.push(n);
                }
            }
            // carry impls for this type.
            for imp in &pools.impls {
                if self_type_name(imp).as_deref() == Some(name.as_str()) {
                    let text = render_item(&Item::Impl(imp.clone()));
                    let key = format!("impl:{}:{:x}", name, hash_str(&text));
                    push_carried(&mut support, &mut seen_keys, key, text);
                    // recurse into the impl body's references.
                    let inner = collect_idents_item(&Item::Impl(imp.clone()));
                    let inner_generics = generics_params(&imp.generics);
                    for n in inner.names {
                        if !inner_generics.contains(&n) {
                            work.push(n);
                        }
                    }
                    if let Some(tn) = impl_trait_name(imp) {
                        work.push(tn);
                    }
                }
            }
            continue;
        }

        if let Some(item) = pools.consts.get(&name) {
            push_carried(
                &mut support,
                &mut seen_keys,
                format!("const:{}", name),
                render_item_pub(item),
            );
            for n in collect_idents_item(item).names {
                work.push(n);
            }
            continue;
        }

        if let Some(helper) = pools.fns.get(&name) {
            // carry a helper free function (kept with its original name).
            let text = render_item_pub(&Item::Fn(helper.clone()));
            push_carried(&mut support, &mut seen_keys, format!("fn:{}", name), text);
            let inner_generics = fn_generic_params(helper);
            for n in collect_idents_fn(helper).names {
                if !inner_generics.contains(&n) {
                    work.push(n);
                }
            }
            continue;
        }
        // else: not file-local -> assume std/primitive/generic; ignore.
    }

    // Carry the file's use-imports — but drop any import rooted at a file-local
    // item that this unit did NOT pull into its support closure. Otherwise an
    // isolated unit inherits an unresolvable `use Local::...;` (e.g. a bystander
    // `use List::Cons;`) and fails the rustc gate, which in turn defeats
    // function-list bisection down to a single culprit.
    for (root, c) in uses {
        if let Some(r) = root {
            let is_local = pools.types.contains_key(r)
                || pools.consts.contains_key(r)
                || pools.fns.contains_key(r);
            if is_local {
                let carried = seen_keys.contains(&format!("type:{}", r))
                    || seen_keys.contains(&format!("const:{}", r))
                    || seen_keys.contains(&format!("fn:{}", r));
                if !carried {
                    continue;
                }
            }
        }
        push_carried(&mut support, &mut seen_keys, c.key.clone(), c.text.clone());
    }

    Some(Unit {
        orig_name: self_name,
        seed_file: PathBuf::new(),
        func: f.clone(),
        support,
    })
}

fn item_generics(item: &Item) -> BTreeSet<String> {
    match item {
        Item::Struct(s) => generics_params(&s.generics),
        Item::Enum(e) => generics_params(&e.generics),
        Item::Union(u) => generics_params(&u.generics),
        Item::Type(t) => generics_params(&t.generics),
        Item::Trait(t) => generics_params(&t.generics),
        _ => BTreeSet::new(),
    }
}

fn push_carried(
    support: &mut Vec<Carried>,
    seen: &mut BTreeSet<String>,
    key: String,
    text: String,
) {
    if seen.insert(key.clone()) {
        support.push(Carried {
            key,
            text: text.trim_end().to_string(),
        });
    }
}

fn hash_str(s: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

// ---------------------------------------------------------------------------
// Packing
// ---------------------------------------------------------------------------

/// A function placed into a pack: its final name, provenance, and line span in
/// the emitted `lib.rs` (1-based, inclusive).
#[derive(Clone, Debug, Serialize)]
pub struct PackedFn {
    pub index: usize,
    pub final_name: String,
    pub provenance: Provenance,
    pub line_start: usize,
    pub line_end: usize,
}

/// Attribution of a source line range to the units that depend on it.
#[derive(Clone, Debug)]
struct Segment {
    line_start: usize,
    line_end: usize,
    /// unit indices that "own" this segment (a primary owns exactly itself; a
    /// shared prelude item is owned by every unit that needs it).
    owners: BTreeSet<usize>,
}

/// A packed crate ready for the pipeline.
pub struct Pack {
    pub crate_id: String,
    pub source: String,
    pub functions: Vec<PackedFn>,
    segments: Vec<Segment>,
}

impl Pack {
    /// Map a 1-based source line to the set of unit indices that own it.
    pub fn units_at_line(&self, line: usize) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        for seg in &self.segments {
            if line >= seg.line_start && line <= seg.line_end {
                out.extend(seg.owners.iter().copied());
            }
        }
        out
    }

    /// The provenance list for logging.
    pub fn provenances(&self) -> Vec<&Provenance> {
        self.functions.iter().map(|f| &f.provenance).collect()
    }
}

/// A unit paired with the provenance to record (mutation chain filled in by the
/// caller after mutation).
#[derive(Clone)]
pub struct PackInput {
    pub unit: Unit,
    pub provenance: Provenance,
}

/// Pack a set of units into one crate. Support items are emitted once (deduped)
/// in a shared prelude; a support item conflict (same key, different text)
/// causes the *later* unit needing it to be dropped from the pack.
pub fn pack(inputs: &[PackInput], crate_id: &str) -> Pack {
    // Assign a stable index per input.
    // First pass: resolve the shared prelude and which units survive.
    let mut prelude_items: Vec<(String, String)> = Vec::new(); // (key, text)
    let mut key_to_text: BTreeMap<String, String> = BTreeMap::new();
    let mut key_deps: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut kept: Vec<usize> = Vec::new();

    for (i, inp) in inputs.iter().enumerate() {
        // Check every support item for a conflict.
        let mut conflict = false;
        for c in &inp.unit.support {
            if let Some(existing) = key_to_text.get(&c.key) {
                if existing != &c.text {
                    conflict = true;
                    break;
                }
            }
        }
        if conflict {
            continue;
        }
        // Commit this unit's support.
        for c in &inp.unit.support {
            if !key_to_text.contains_key(&c.key) {
                key_to_text.insert(c.key.clone(), c.text.clone());
                prelude_items.push((c.key.clone(), c.text.clone()));
            }
            key_deps.entry(c.key.clone()).or_default().insert(i);
        }
        kept.push(i);
    }

    // Deterministic prelude order: sort by key.
    prelude_items.sort_by(|a, b| a.0.cmp(&b.0));

    // Second pass: build the source with a line cursor.
    let mut source = String::new();
    let mut segments: Vec<Segment> = Vec::new();
    let header = "// AUTO-GENERATED fuzz pack. Do not edit.\n#![allow(dead_code, unused_variables, unused_mut, unused_parens, unused_imports, non_snake_case, unreachable_code, path_statements, unused_assignments)]\n\n";
    source.push_str(header);
    let mut cursor = count_lines(header); // lines consumed so far

    // Prelude.
    for (key, text) in &prelude_items {
        let block = format!("{}\n\n", text);
        let start = cursor + 1;
        source.push_str(&block);
        cursor += count_lines(&block);
        let end = cursor;
        let owners = key_deps.get(key).cloned().unwrap_or_default();
        segments.push(Segment {
            line_start: start,
            line_end: end,
            owners,
        });
    }

    // Primary functions.
    let mut functions = Vec::new();
    for &i in &kept {
        let inp = &inputs[i];
        let final_name = sanitize_name(i, &inp.unit.orig_name);
        let rendered = render_primary(&inp.unit.func, &final_name);
        let block = format!("{}\n", rendered);
        let start = cursor + 1;
        source.push_str(&block);
        cursor += count_lines(&block);
        let end = cursor;
        let mut owners = BTreeSet::new();
        owners.insert(i);
        segments.push(Segment {
            line_start: start,
            line_end: end,
            owners,
        });
        functions.push(PackedFn {
            index: i,
            final_name,
            provenance: inp.provenance.clone(),
            line_start: start,
            line_end: end,
        });
    }

    Pack {
        crate_id: crate_id.to_string(),
        source,
        functions,
        segments,
    }
}

fn sanitize_name(index: usize, orig: &str) -> String {
    let cleaned: String = orig
        .chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    format!("f_{}_{}", index, cleaned)
}

fn count_lines(s: &str) -> usize {
    s.bytes().filter(|&b| b == b'\n').count()
}

/// Parse a standalone `.rs` file into units (for the `one`/`minimize` paths).
pub fn units_from_source(text: &str, seed_file: &Path) -> Result<Vec<Unit>> {
    let file: syn::File = syn::parse_file(text).context("syn parse failed")?;
    let pools = build_pools(&file);
    let use_items = build_use_items(&pools);
    let mut units = Vec::new();
    for f in pools.fns.values() {
        if let Some(mut unit) = extract_one_unit(f, &pools, &use_items) {
            unit.seed_file = seed_file.to_path_buf();
            units.push(unit);
        }
    }
    units.sort_by(|a, b| a.orig_name.cmp(&b.orig_name));
    Ok(units)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unit_from(src: &str, fname: &str) -> Unit {
        let units = units_from_source(src, Path::new("test.rs")).unwrap();
        units.into_iter().find(|u| u.orig_name == fname).unwrap()
    }

    #[test]
    fn extract_simple_fn() {
        let src = "pub fn add(a: u32, b: u32) -> u32 { a + b }";
        let u = unit_from(src, "add");
        assert_eq!(u.orig_name, "add");
        assert!(u.support.is_empty());
    }

    #[test]
    fn carries_struct_dep() {
        let src = "\
struct Point { x: u32, y: u32 }
pub fn mk() -> Point { Point { x: 1, y: 2 } }
";
        let u = unit_from(src, "mk");
        assert!(u.support.iter().any(|c| c.key == "type:Point"));
        // rendered dep must be pub.
        assert!(u
            .support
            .iter()
            .any(|c| c.key == "type:Point" && c.text.contains("pub struct Point")));
    }

    #[test]
    fn carries_impl_and_helper() {
        let src = "\
struct S { n: u32 }
impl S { fn get(&self) -> u32 { self.n } }
fn helper(x: u32) -> u32 { x + 1 }
pub fn use_it(s: S) -> u32 { helper(s.get()) }
";
        let u = unit_from(src, "use_it");
        assert!(u.support.iter().any(|c| c.key == "type:S"));
        assert!(u.support.iter().any(|c| c.key.starts_with("impl:S")));
        assert!(u.support.iter().any(|c| c.key == "fn:helper"));
    }

    #[test]
    fn bystander_local_use_not_carried() {
        // `use List::Cons;` is a file-level import of a file-local enum. A
        // function that does not touch `List` must NOT inherit that import, or it
        // won't compile in isolation.
        let src = "\
enum List { Cons(u8), Nil }
use List::Cons;
use std::vec::Vec;
pub fn touches(x: &mut u8) -> u8 { *x }
";
        let u = unit_from(src, "touches");
        assert!(
            !u.support.iter().any(|c| c.text.contains("use List :: Cons")
                || c.text.contains("use List::Cons")),
            "bystander local import should be dropped: {:?}",
            u.support.iter().map(|c| &c.key).collect::<Vec<_>>()
        );
        // An external import (std) is still carried.
        assert!(u.support.iter().any(|c| c.key.starts_with("use:")
            && c.text.contains("Vec")));
    }

    #[test]
    fn rejects_crate_paths() {
        let src = "pub fn f() -> u32 { crate::other::THING }";
        let units = units_from_source(src, Path::new("t.rs")).unwrap();
        assert!(units.is_empty(), "crate:: path fn should be dropped");
    }

    #[test]
    fn pack_renames_and_maps_lines() {
        let u1 = unit_from("pub fn add(a: u32, b: u32) -> u32 { a + b }", "add");
        let u2 = unit_from("pub fn sub(a: u32, b: u32) -> u32 { a - b }", "sub");
        let inputs = vec![
            PackInput {
                provenance: u1.provenance(),
                unit: u1,
            },
            PackInput {
                provenance: u2.provenance(),
                unit: u2,
            },
        ];
        let pack = pack(&inputs, "c0");
        assert!(pack.source.contains("pub fn f_0_add"));
        assert!(pack.source.contains("pub fn f_1_sub"));
        assert_eq!(pack.functions.len(), 2);
        // line mapping: a line inside f_1_sub maps to unit index 1.
        let f1 = &pack.functions[1];
        let owners = pack.units_at_line(f1.line_start);
        assert!(owners.contains(&1));
        assert!(!owners.contains(&0));
    }

    #[test]
    fn shared_prelude_dedup() {
        // two units carrying the same struct -> one prelude copy, owned by both.
        let mut a = unit_from(
            "struct P { x: u32 }\npub fn f() -> P { P { x: 1 } }",
            "f",
        );
        a.orig_name = "f".into();
        let mut b = unit_from(
            "struct P { x: u32 }\npub fn g() -> P { P { x: 2 } }",
            "g",
        );
        b.orig_name = "g".into();
        let inputs = vec![
            PackInput {
                provenance: a.provenance(),
                unit: a,
            },
            PackInput {
                provenance: b.provenance(),
                unit: b,
            },
        ];
        let pack = pack(&inputs, "c1");
        let count = pack.source.matches("struct P").count();
        assert_eq!(count, 1, "struct P should be emitted once");
        assert_eq!(pack.functions.len(), 2);
    }
}
