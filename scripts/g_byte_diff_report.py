#!/usr/bin/env python3
"""
G_byte divergence report.

Runs mainline `aeneas -backend lean` (L₀) and our `aeneas-check` (L₁)
on every fixture under tests/llbc/, slices both .lean outputs into
per-decl chunks, computes the diff for each divergent pair, and
heuristic-categorises the divergence into a "pattern". Aggregates
counts and emits a Markdown report ranked by pattern frequency.

The point: show every bug between our cert-walker's emit and mainline
Aeneas's emit, wholesale — independent of whether the output
typechecks. Use the ranked output to pick the highest-leverage
divergence pattern to fix first.

Usage:
    python3 scripts/g_byte_diff_report.py [--out REPORT.md] [--limit N]
"""

import argparse
import difflib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from collections import defaultdict, Counter

ROOT = Path(__file__).resolve().parents[1]
AENEAS = ROOT / "src" / "_build" / "default" / "main.exe"
AENEAS_CHECK = ROOT / "aeneas-lean-checker" / ".lake" / "build" / "bin" / "aeneas-check"
FIXTURES = ROOT / "tests" / "llbc"

DECL_HEADERS = ("def ", "abbrev ", "structure ", "inductive ", "class ",
                "instance ", "theorem ", "example ", "opaque ")


def slice_by_decl(text):
    """Slice .lean text into (decl_name, slice_text) chunks.

    A "decl block" runs from the decl-header line (def/abbrev/...)
    forward, ending before any trailing chrome (blank lines,
    docstring `/-- … -/` blocks, `@[…]` attribute lines) that
    belong to the *next* decl. We do this by scanning forward to
    the next header, then trimming trailing chrome lines from the
    slice. Returns a list preserving file order.
    """
    starts = []
    offset = 0
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        for kw in DECL_HEADERS:
            if stripped.startswith(kw):
                rest = stripped[len(kw):].lstrip()
                m = re.match(r"([@A-Za-z_][\w.]*)", rest)
                if m:
                    starts.append((offset, m.group(1)))
                break
        offset += len(line)

    out = []
    for i, (start, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        slice_text = text[start:end]
        # Trim trailing chrome lines (blank, attribute, docstring).
        slice_lines = slice_text.splitlines(keepends=True)
        in_doc = False
        # Walk backward; drop lines while they look like chrome.
        while slice_lines:
            tail = slice_lines[-1].strip()
            if tail == "":
                slice_lines.pop()
                continue
            if tail.startswith("@["):
                slice_lines.pop()
                continue
            if tail.endswith("-/") and "/-" in tail:
                # Single-line docstring on its own line.
                slice_lines.pop()
                continue
            if tail.endswith("-/"):
                # End of a multi-line doc block — drop it plus prior
                # lines up to the `/--` or `/-`.
                slice_lines.pop()
                while slice_lines:
                    t = slice_lines[-1].strip()
                    slice_lines.pop()
                    if t.startswith("/--") or t.startswith("/-"):
                        break
                continue
            break
        out.append((name, "".join(slice_lines)))
    return out


def run_l0(llbc, dest):
    dest.mkdir(parents=True, exist_ok=True)
    r = subprocess.run([str(AENEAS), "-backend", "lean", "-dest", str(dest), str(llbc)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    # Pick the largest .lean (mainline emits multiple; we want the
    # combined). Walk dest recursively.
    leans = list(dest.rglob("*.lean"))
    if not leans:
        return None, "no .lean emitted"
    leans.sort(key=lambda p: p.stat().st_size)
    text = "\n".join(p.read_text() for p in leans)
    return text, None


def run_l1(cert, out_path):
    r = subprocess.run([str(AENEAS_CHECK), str(cert), "--out", str(out_path)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr
    return out_path.read_text(), None


# ---------------------------------------------------------------
# Pattern detection.
# ---------------------------------------------------------------

def categorise(l0_slice, l1_slice):
    """Return a coarse pattern name describing the divergence.

    Patterns checked in order — the first match wins. Heuristic; the
    point is to bucket so the user can attack the most-common pattern
    first, not to be perfectly precise.
    """
    if l0_slice == l1_slice:
        return None  # not divergent at the slice level

    l0_lines = l0_slice.splitlines()
    l1_lines = l1_slice.splitlines()

    # Trim trailing whitespace and compare again — sometimes the only
    # difference is line-ending or trailing-space hygiene.
    if [l.rstrip() for l in l0_lines] == [l.rstrip() for l in l1_lines]:
        return "trailing_whitespace_only"

    # Strip leading whitespace per line.
    if [l.strip() for l in l0_lines] == [l.strip() for l in l1_lines]:
        return "indent_only"

    l0_text = l0_slice
    l1_text = l1_slice

    # Comment-only differences: strip all `/-- ... -/` blocks and
    # `--` line comments, then re-compare.
    def strip_comments(t):
        t = re.sub(r"/--.*?-/", "", t, flags=re.DOTALL)
        t = re.sub(r"/-.*?-/", "", t, flags=re.DOTALL)
        t = re.sub(r"--[^\n]*", "", t)
        return re.sub(r"\s+", " ", t).strip()
    if strip_comments(l0_text) == strip_comments(l1_text):
        return "comment_only"

    # Structure-vs-tuple-collapse: L0 has `def X := A × B × ...`,
    # L1 has `structure X where ...`.
    if "structure " in l1_text and re.search(r"def \w+ :=\s*\S+\s*×", l0_text):
        return "tuple_collapse"
    if "structure " in l0_text and re.search(r"def \w+ :=\s*\S+\s*×", l1_text):
        return "tuple_expand"

    # Placeholder-emit shapes specific to our cert-walker.
    if ".placeholder" in l1_text and ".placeholder" not in l0_text:
        return "l1_placeholder_emit"

    # Type ascription via our `__typed::` shape.
    if " : Option " in l1_text and " : Option " not in l0_text and "((" in l1_text:
        return "l1_type_ascription"
    if "((" in l1_text and " : " in l1_text and "((" not in l0_text:
        return "l1_type_ascription"

    # Cast head: mainline `UScalar.hcast` / `Scalar.cast`, ours `((x : Std.T))`.
    if "UScalar.hcast" in l0_text or "Scalar.cast" in l0_text:
        if "UScalar.hcast" not in l1_text and "Scalar.cast" not in l1_text:
            return "cast_shape"

    # Different binding name: only differs by `tN` numbers.
    def renumber(s):
        return re.sub(r"\bt\d+\b", "tN", s)
    if renumber(l0_text) == renumber(l1_text):
        return "binding_name_renumber"

    # Backward-closure shape mismatch on `&mut self` impl methods.
    # Mainline produces `Result (T × (T → U))` (value + backward);
    # ours often produces `Result T` or `Result (T × (Unit → U))`.
    l0_has_back = bool(re.search(r"× \(\S.* → ", l0_text))
    l1_has_back = bool(re.search(r"× \(\S.* → ", l1_text))
    if l0_has_back and not l1_has_back:
        return "missing_backward_closure"
    if l0_has_back and l1_has_back and ("Unit →" in l1_text and "Unit →" not in l0_text):
        return "wrong_backward_closure_domain"

    # `cont` payload shape (Bug 4e-related).
    if " cont (" in l1_text and " cont " in l0_text and " cont (" not in l0_text:
        return "cont_payload_tuple"
    if " cont " in l1_text and " cont (" in l0_text and " cont (" not in l1_text:
        return "cont_payload_missing_tuple"

    # `let ... ←` vs `let ... :=` — bind shape.
    n0_arrow = l0_text.count("←")
    n1_arrow = l1_text.count("←")
    if abs(n0_arrow - n1_arrow) > 0:
        return "bind_arrow_count_diff"

    # Different number of decls inside (a structure's field count or
    # an inductive's variant count).
    if l0_text.count(":=") != l1_text.count(":="):
        return "decl_body_size_diff"

    # Reordered fields/binds: same multiset of lines, different
    # order. Detect via Counter comparison after stripping whitespace.
    if (Counter(l.strip() for l in l0_lines if l.strip()) ==
        Counter(l.strip() for l in l1_lines if l.strip())):
        return "reorder_only"

    # Catch-all.
    return "other"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="/tmp/g_byte_report.md")
    ap.add_argument("--limit", type=int, default=None,
                    help="cap number of fixtures (for fast iteration)")
    ap.add_argument("--include-pass", action="store_true",
                    help="include byte-pass fixtures in the report")
    args = ap.parse_args()

    fixtures = sorted(FIXTURES.glob("*.cert.json"))
    if args.limit:
        fixtures = fixtures[:args.limit]

    pattern_counts = Counter()
    pattern_examples = defaultdict(list)
    fixture_summary = []  # (fixture, status, pattern_counter)
    l0_fail = []
    l1_fail = []
    file_identical = 0

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for i, cert in enumerate(fixtures, 1):
            fx = cert.name.removesuffix(".cert.json")
            print(f"[{i}/{len(fixtures)}] {fx}", file=sys.stderr)
            llbc = cert.with_suffix("").with_suffix(".llbc")
            if not llbc.exists():
                print(f"  skip: no .llbc next to {cert}", file=sys.stderr)
                continue

            l0_dir = tmp / fx / "l0"
            l1_path = tmp / fx / "l1.lean"
            l1_path.parent.mkdir(parents=True, exist_ok=True)

            l0_text, l0_err = run_l0(llbc, l0_dir)
            if l0_text is None:
                l0_fail.append((fx, (l0_err or "").splitlines()[0] if l0_err else ""))
                continue

            l1_text, l1_err = run_l1(cert, l1_path)
            if l1_text is None:
                l1_fail.append((fx, (l1_err or "").splitlines()[0] if l1_err else ""))
                continue

            if l0_text == l1_text:
                file_identical += 1
                fixture_summary.append((fx, "pass-file", Counter()))
                continue

            l0_slices = dict(slice_by_decl(l0_text))
            l1_slices = dict(slice_by_decl(l1_text))

            shared = set(l0_slices) & set(l1_slices)
            only_l0 = set(l0_slices) - set(l1_slices)
            only_l1 = set(l1_slices) - set(l0_slices)

            fx_counts = Counter()
            for name in only_l0:
                fx_counts["only_in_L0"] += 1
                pattern_counts["only_in_L0"] += 1
                if len(pattern_examples["only_in_L0"]) < 3:
                    pattern_examples["only_in_L0"].append((fx, name, l0_slices[name][:200], ""))
            for name in only_l1:
                fx_counts["only_in_L1"] += 1
                pattern_counts["only_in_L1"] += 1
                if len(pattern_examples["only_in_L1"]) < 3:
                    pattern_examples["only_in_L1"].append((fx, name, "", l1_slices[name][:200]))

            for name in sorted(shared):
                pat = categorise(l0_slices[name], l1_slices[name])
                if pat is None:
                    continue
                fx_counts[pat] += 1
                pattern_counts[pat] += 1
                if len(pattern_examples[pat]) < 3:
                    # Limit example size.
                    pattern_examples[pat].append(
                        (fx, name, l0_slices[name][:400], l1_slices[name][:400]))

            if fx_counts:
                fixture_summary.append((fx, "divergent", fx_counts))
            else:
                fixture_summary.append((fx, "pass-decls", Counter()))

    # ----- emit report -----
    lines = []
    lines.append(f"# G_byte divergence report")
    lines.append(f"")
    lines.append(f"Compared {len(fixtures)} fixtures' L₀ (mainline `aeneas -backend lean`) "
                 f"vs L₁ (our `aeneas-check`) emit, per-decl.")
    lines.append(f"")
    lines.append(f"## Topline")
    lines.append(f"")
    lines.append(f"- File-level byte-identical: **{file_identical}**")
    lines.append(f"- L₀ emit failed: **{len(l0_fail)}**")
    lines.append(f"- L₁ emit failed: **{len(l1_fail)}**")
    div_fixtures = sum(1 for _, st, _ in fixture_summary if st == "divergent")
    lines.append(f"- Divergent fixtures: **{div_fixtures}**")
    lines.append(f"- Total divergent (decl, fixture) pairs: **{sum(pattern_counts.values())}**")
    lines.append(f"")

    lines.append(f"## Patterns by frequency")
    lines.append(f"")
    lines.append(f"| Pattern | Count | What it means |")
    lines.append(f"|---|---|---|")
    descs = {
        "trailing_whitespace_only": "Trailing-whitespace hygiene only.",
        "indent_only": "Differs only by leading whitespace.",
        "comment_only": "Differs only inside docstrings / line comments.",
        "tuple_collapse": "L₀ collapses a unit-field struct to a `def NAME := A × B`; L₁ keeps `structure`.",
        "tuple_expand": "L₁ has a tuple-def shape; L₀ keeps `structure`.",
        "l1_placeholder_emit": "L₁ emits a `.placeholder` shim (Bug 4d/4f); L₀ has the real value.",
        "l1_type_ascription": "L₁ wraps a value in `((<x> : <ty>))` (Bug 4f `__typed::`); L₀ doesn't.",
        "cast_shape": "L₀ uses `UScalar.hcast` / `Scalar.cast`; L₁ uses our `__cast::` rendering.",
        "binding_name_renumber": "Only `tN` binding numbers differ.",
        "cont_payload_tuple": "L₁ packs `cont (a, b)`; L₀ has bare `cont a`.",
        "cont_payload_missing_tuple": "L₀ packs `cont (a, b)`; L₁ has bare `cont a`.",
        "bind_arrow_count_diff": "Different number of `←` monadic binds.",
        "decl_body_size_diff": "Different number of `:=` definitions inside the slice.",
        "reorder_only": "Same lines in different order.",
        "only_in_L0": "Decl emitted by mainline only.",
        "only_in_L1": "Decl emitted by our cert-walker only.",
        "other": "Catch-all — not matched by any heuristic.",
    }
    for pat, n in pattern_counts.most_common():
        lines.append(f"| `{pat}` | {n} | {descs.get(pat, '')} |")
    lines.append(f"")

    lines.append(f"## Examples (up to 3 per pattern)")
    lines.append(f"")
    for pat, _ in pattern_counts.most_common():
        lines.append(f"### `{pat}`")
        lines.append(f"")
        for fx, name, l0, l1 in pattern_examples[pat]:
            lines.append(f"<details><summary><code>{fx}</code> · `{name}`</summary>")
            lines.append(f"")
            lines.append(f"**L₀ (mainline):**")
            lines.append("```lean")
            lines.append(l0.rstrip())
            lines.append("```")
            lines.append(f"")
            lines.append(f"**L₁ (ours):**")
            lines.append("```lean")
            lines.append(l1.rstrip())
            lines.append("```")
            lines.append(f"")
            if pat not in ("only_in_L0", "only_in_L1"):
                diff = "\n".join(difflib.unified_diff(
                    l0.splitlines(), l1.splitlines(),
                    lineterm="", fromfile="L0", tofile="L1", n=2))
                lines.append(f"**Diff:**")
                lines.append("```diff")
                lines.append(diff)
                lines.append("```")
                lines.append(f"")
            lines.append(f"</details>")
            lines.append(f"")

    if l0_fail or l1_fail:
        lines.append(f"## Emit failures")
        lines.append(f"")
        if l0_fail:
            lines.append(f"### L₀ (mainline aeneas) failures: {len(l0_fail)}")
            for fx, err in l0_fail[:20]:
                lines.append(f"- `{fx}`: {err}")
            lines.append(f"")
        if l1_fail:
            lines.append(f"### L₁ (aeneas-check) failures: {len(l1_fail)}")
            for fx, err in l1_fail[:20]:
                lines.append(f"- `{fx}`: {err}")
            lines.append(f"")

    lines.append(f"## Per-fixture summary")
    lines.append(f"")
    lines.append(f"| Fixture | Status | Top pattern | Other patterns |")
    lines.append(f"|---|---|---|---|")
    for fx, status, ctr in sorted(fixture_summary, key=lambda r: -sum(r[2].values())):
        top = ctr.most_common(1)[0] if ctr else ("-", 0)
        rest = ", ".join(f"`{p}`({n})" for p, n in ctr.most_common()[1:5])
        lines.append(f"| `{fx}` | {status} | `{top[0]}`({top[1]}) | {rest} |")

    Path(args.out).write_text("\n".join(lines) + "\n")
    print(f"wrote {args.out}", file=sys.stderr)
    # Also print the patterns table to stdout for quick triage.
    print()
    print("## Patterns by frequency")
    for pat, n in pattern_counts.most_common():
        print(f"  {n:>5}  {pat}")
    print()
    print(f"File-identical: {file_identical}")
    print(f"L0-fail: {len(l0_fail)}  L1-fail: {len(l1_fail)}")


if __name__ == "__main__":
    main()
