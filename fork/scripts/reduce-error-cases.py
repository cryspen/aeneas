#!/usr/bin/env python3
"""Reduce the Lean `Aeneas.Std.Error` enum to the cases that behave differently.

The Lean library models Rust failures with a 7-constructor `Error` enum. Every one
of `integerOverflow`, `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`
and `assertionFailure` is just a Rust panic, so they are all collapsed into
`panic`, leaving only the genuine distinction between a panic and UB:

    inductive Error where
       | panic: Error
       | undef: Error

Which constructors go and which survive is the `REMOVED`/`KEPT` configuration
below; the passes are driven by it rather than hardcoding a case count.

This script performs the whole rewrite mechanically so that it can be re-applied
after a rebase or against a different fork/worktree of aeneas.

Usage:
    ./reduce-error-cases.py [REPO_ROOT] [--check] [--quiet]
    ./reduce-error-cases.py [REPO_ROOT] --fix-guard-msgs [LEAN_FILE ...]

    REPO_ROOT          aeneas checkout to patch (default: search upwards from $PWD)
    --check            report what would change, write nothing (exit 1 if not applied)
    --quiet            only print the summary
    --fix-guard-msgs   re-wrap `#guard_msgs` expectations (see below); needs a built
                       `backends/lean` (run `lake build` first)

`#guard_msgs` docstrings pin Lean's pretty-printed output, and `Error.panic` is
shorter than the constructors it replaces, so the line wrapping of those expected
messages changes. `--fix-guard-msgs` runs `lake env lean --json` on the affected
files and rewrites each mismatching docstring with the message Lean actually
produced, so the whole migration stays a single scripted run. It refuses to touch
a docstring whose content differs by anything other than whitespace: re-flowing
line breaks is safe, but a changed *statement* means the reduced enum changed what
a spec says, and that needs a human.

    ./reduce-error-cases.py /path/to/checkout
    cd /path/to/checkout/backends/lean && lake build      # may fail on #guard_msgs
    ./reduce-error-cases.py /path/to/checkout --fix-guard-msgs
    cd /path/to/checkout/backends/lean && lake build      # green

The script is idempotent: running it on an already-reduced tree is a no-op.
Every non-mechanical rewrite is anchored on a piece of source text; if an anchor
is gone (because upstream moved the code) the script fails loudly with the file
and the text it was looking for, rather than silently skipping it.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

#: Constructors that go away, and the constructor they are folded into.
REMOVED = {
    "integerOverflow": "panic",
    "divisionByZero": "panic",
    "arrayOutOfBounds": "panic",
    "maximumSizeExceeded": "panic",
    "assertionFailure": "panic",
}

#: Constructors of the reduced enum, in declaration order.
KEPT = ["panic", "undef"]

#: File holding the `inductive Error` declaration, relative to the repo root.
PRIMITIVES = Path("backends/lean/Aeneas/Std/Primitives.lean")

#: File holding the `error_pred_eq_disj` helper lemma.
STEP_INIT = Path("backends/lean/Aeneas/Tactic/Step/Init.lean")

#: Directories scanned for Lean sources.
LEAN_ROOTS = [Path("backends/lean"), Path("tests/lean")]

ALL_CTORS = KEPT + list(REMOVED)
_CTOR_RE = re.compile(r"\b(" + "|".join(map(re.escape, REMOVED)) + r")\b")


# ---------------------------------------------------------------------------
# Infrastructure
# ---------------------------------------------------------------------------


class PatchError(Exception):
    """A rewrite could not be applied because its anchor was not found."""


@dataclass
class Run:
    root: Path
    check: bool
    quiet: bool
    edits: dict[Path, int] = field(default_factory=dict)  # path -> #changes
    notes: list[str] = field(default_factory=list)

    def log(self, msg: str) -> None:
        if not self.quiet:
            print(msg)

    def read(self, path: Path) -> str:
        return path.read_text(encoding="utf-8")

    def write(self, path: Path, old: str, new: str, changes: int, what: str) -> None:
        if old == new:
            return
        rel = path.relative_to(self.root)
        self.edits[rel] = self.edits.get(rel, 0) + changes
        self.log(f"  {rel}: {what}")
        if not self.check:
            path.write_text(new, encoding="utf-8")


def lean_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for sub in LEAN_ROOTS:
        d = root / sub
        if d.is_dir():
            files += [p for p in sorted(d.rglob("*.lean")) if ".lake" not in p.parts]
    return files


def find_root(argv_root: str | None) -> Path:
    if argv_root:
        root = Path(argv_root).resolve()
        if not (root / PRIMITIVES).is_file():
            sys.exit(f"error: {root} does not look like an aeneas checkout "
                     f"(missing {PRIMITIVES})")
        return root
    here = Path.cwd().resolve()
    for cand in [here, *here.parents]:
        if (cand / PRIMITIVES).is_file():
            return cand
    sys.exit("error: could not find an aeneas checkout above the current directory; "
             "pass the repository root explicitly")


# ---------------------------------------------------------------------------
# Pass 1: shrink the `inductive Error` declaration
# ---------------------------------------------------------------------------


def shrink_inductive(run: Run) -> None:
    path = run.root / PRIMITIVES
    text = run.read(path)

    m = re.search(r"^inductive Error where\n((?:[ \t]*\|.*\n)+)", text, re.M)
    if m is None:
        raise PatchError(f"{PRIMITIVES}: could not find the `inductive Error where` block")

    body = m.group(1)
    declared = re.findall(r"\|\s*([A-Za-z_][A-Za-z0-9_'!?]*)", body)
    unknown = [c for c in declared if c not in ALL_CTORS]
    if unknown:
        raise PatchError(
            f"{PRIMITIVES}: `Error` has constructor(s) this script does not know about: "
            f"{', '.join(unknown)}; update REMOVED/KEPT before re-running")

    if not any(c in REMOVED for c in declared):
        run.log(f"  {PRIMITIVES}: `Error` already reduced")
        return

    new_body = "".join(f"   | {c}: Error\n" for c in KEPT)
    new_text = text[: m.start(1)] + new_body + text[m.end(1) :]
    dropped = [c for c in declared if c in REMOVED]
    run.write(path, text, new_text, len(dropped),
              f"dropped {', '.join(dropped)} from `inductive Error`")


# ---------------------------------------------------------------------------
# Pass 2: merge match arms that would collide after the rename
# ---------------------------------------------------------------------------
#
# Failure postconditions of `partialSpec` are written as anonymous matches:
#
#     (fun | .divisionByZero => (↑y : Int) = 0
#          | .integerOverflow => (↑x : Int) = min ∧ (↑y : Int) = -1
#          | _ => False)
#
# Once both constructors become `.panic` the two arms collide (the second one
# becomes dead code), so they have to be merged into a single arm whose body is
# the disjunction of the original bodies.


_FUN_MATCH_RE = re.compile(r"\(fun\s*\|")


def _matching_paren(text: str, open_idx: int) -> int:
    depth = 0
    i = open_idx
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        elif c == '"':  # skip string literals
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        i += 1
    raise PatchError("unbalanced parentheses while scanning a `fun |` match")


def _split_arms(body: str) -> list[tuple[str, str]] | None:
    """Split `| p => e | p => e` into (pattern, body) pairs at nesting depth 0."""
    depth = 0
    parts: list[str] = []
    cur: list[str] = []
    i = 0
    while i < len(body):
        c = body[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "|" and depth == 0:
            # `|` also occurs in `‖`/`∨`-free positions only; a real arm separator
            # is not part of a `||` operator.
            if body[i : i + 2] == "||" or (i > 0 and body[i - 1] == "|"):
                i += 1
                continue
            parts.append("".join(cur))
            cur = []
            i += 1
            continue
        cur.append(c)
        i += 1
    parts.append("".join(cur))

    arms: list[tuple[str, str]] = []
    for part in parts[1:]:  # parts[0] is the text before the first `|`
        if "=>" not in part:
            return None
        pat, rhs = part.split("=>", 1)
        arms.append((pat.strip(), " ".join(rhs.split())))
    return arms or None


def _canonical_pattern(pat: str) -> str | None:
    """Map an arm pattern to the constructor it matches after the rename."""
    m = re.fullmatch(r"(?:\.|Error\.)?([A-Za-z_][A-Za-z0-9_'!?]*)", pat)
    if m is None:
        return None
    name = m.group(1)
    if name in REMOVED:
        return "." + REMOVED[name]
    if name in KEPT:
        return "." + name
    return None  # `_`, a variable binder, or something we do not understand


def merge_colliding_arms(run: Run, path: Path) -> None:
    text = run.read(path)
    out = text
    merged = 0

    pos = 0
    while True:
        m = _FUN_MATCH_RE.search(out, pos)
        if m is None:
            break
        open_idx = m.start()
        try:
            close_idx = _matching_paren(out, open_idx)
        except PatchError:
            pos = m.end()
            continue
        whole = out[open_idx : close_idx + 1]
        inner = whole[len("(fun") : -1]
        arms = _split_arms(inner)
        if arms is None:
            pos = m.end()
            continue

        # Only touch matches on `Error`: every arm must be a known constructor
        # or the catch-all `_`.
        canon: list[str | None] = []
        for pat, _rhs in arms:
            if pat == "_":
                canon.append(None)
            else:
                c = _canonical_pattern(pat)
                if c is None:
                    canon = []
                    break
                canon.append(c)
        if not canon or not any(c is not None for c in canon):
            pos = m.end()
            continue

        # Group arms by their post-rename pattern, preserving order.
        groups: list[tuple[str | None, list[str]]] = []
        for (pat, rhs), c in zip(arms, canon):
            key = c if c is not None else "_"
            if groups and groups[-1][0] == key:
                groups[-1][1].append(rhs)
            else:
                existing = next((g for g in groups if g[0] == key), None)
                if existing is not None:
                    existing[1].append(rhs)
                else:
                    groups.append((key, [rhs]))
        if all(len(bodies) == 1 for _key, bodies in groups):
            pos = m.end()  # nothing collides here
            continue

        # Rebuild the match, using the indentation of the original opening `(fun`.
        line_start = out.rfind("\n", 0, open_idx) + 1
        indent = " " * (open_idx - line_start + len("(fun"))
        arm_texts = []
        for key, bodies in groups:
            if len(bodies) == 1:
                rhs = bodies[0]
            else:
                rhs = " ∨ ".join(f"({b})" for b in bodies)
            arm_texts.append(f"| {key} => {rhs}")
        new_whole = "(fun " + ("\n" + indent + " ").join(arm_texts) + ")"
        out = out[:open_idx] + new_whole + out[close_idx + 1 :]
        merged += 1
        pos = open_idx + len(new_whole)

    if merged:
        run.write(path, text, out, merged,
                  f"merged {merged} `Error` match(es) whose arms collide after the rename")


# ---------------------------------------------------------------------------
# Pass 3: regenerate `error_pred_eq_disj`
# ---------------------------------------------------------------------------


def rewrite_error_pred_eq_disj(run: Run) -> None:
    path = run.root / STEP_INIT
    if not path.is_file():
        raise PatchError(f"{STEP_INIT}: file not found")
    text = run.read(path)

    anchor = "theorem error_pred_eq_disj"
    start = text.find(anchor)
    if start < 0:
        raise PatchError(
            f"{STEP_INIT}: could not find `{anchor}`; it enumerates every `Error` "
            "constructor and must be regenerated by hand if it was renamed")

    body_marker = "p = fun e =>\n"
    bstart = text.find(body_marker, start)
    if bstart < 0:
        raise PatchError(f"{STEP_INIT}: `{anchor}` no longer matches `{body_marker.strip()}`")
    bstart += len(body_marker)
    bend = text.find(":= by", bstart)
    if bend < 0:
        raise PatchError(f"{STEP_INIT}: could not find the end of `{anchor}`")

    old_body = text[bstart:bend]
    mentioned = {c for c in ALL_CTORS if re.search(rf"\b{c}\b", old_body)}
    if not (mentioned & set(REMOVED)):
        run.log(f"  {STEP_INIT}: `error_pred_eq_disj` already reduced")
        return

    indent = re.match(r"[ \t]*", old_body).group(0) or "      "
    width = max(len(c) for c in KEPT)
    lines = []
    for i, c in enumerate(KEPT):
        clause = f"(e = .{c.ljust(width)} ∧ p .{c})"
        lines.append(indent + clause + (" ∨" if i + 1 < len(KEPT) else " "))
    new_body = "\n".join(lines)

    new_text = text[:bstart] + new_body + text[bend:]
    run.write(path, text, new_text, 1,
              f"regenerated `error_pred_eq_disj` for {len(KEPT)} constructors")


# ---------------------------------------------------------------------------
# Pass 4: rename the removed constructors, and fix up the prose that named them
# ---------------------------------------------------------------------------


def rename_constructors(run: Run, path: Path) -> None:
    text = run.read(path)
    hits = len(_CTOR_RE.findall(text))
    if not hits:
        return
    new_text = _CTOR_RE.sub(lambda m: REMOVED[m.group(1)], text)
    run.write(path, text, new_text, hits, f"renamed {hits} constructor occurrence(s)")


#: Docs that talk about the constructors in prose rather than by name. The
#: `partialSpec` match syntax no longer separates panics from each other, it
#: separates the surviving `Error`s, so the wording has to follow.
PROSE = {
    "various kinds of panics.": "different kinds of `Error`s.",
}


def rewrite_prose(run: Run, path: Path) -> None:
    text = run.read(path)
    new_text = text
    hits = 0
    for old, new in PROSE.items():
        hits += new_text.count(old)
        new_text = new_text.replace(old, new)
    if not hits:
        return
    run.write(path, text, new_text, hits, f"reworded {hits} doc mention(s)")


# ---------------------------------------------------------------------------
# Pass 5: re-wrap `#guard_msgs` expectations
# ---------------------------------------------------------------------------
#
# `#guard_msgs` compares a docstring against Lean's pretty-printed output. Since
# `Error.panic` is shorter than the constructors it replaces, Lean now fits more
# on a line and the pinned docstrings no longer match — the *content* is right,
# only the wrapping changed. Rather than hand-maintaining those strings (which
# would rot on every rebase) we ask Lean what it prints and write that back.

GUARD_ERR = "Docstring on `#guard_msgs` does not match generated message"
GUARD_MISSING = "Docstring on `#guard_msgs`"  # covers the "no docstring" variants
SEVERITY_PREFIX = {"information": "info", "warning": "warning", "error": "error"}


def _lean_diagnostics(run: Run, rel: Path) -> list[dict] | None:
    """Elaborate a single file and return Lean's JSON diagnostics."""
    lean_dir = run.root / "backends" / "lean"
    env = dict(os.environ)
    elan = Path.home() / ".elan" / "bin"
    if elan.is_dir():
        env["PATH"] = f"{elan}{os.pathsep}{env.get('PATH', '')}"
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "--json", str(rel)],
            cwd=lean_dir, env=env, capture_output=True, text=True)
    except FileNotFoundError:
        raise PatchError("`lake` is not on PATH; --fix-guard-msgs needs the Lean toolchain")
    diags = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            diags.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    if proc.returncode != 0 and not diags:
        run.notes.append(f"{rel}: `lake env lean` failed: "
                         f"{(proc.stderr or proc.stdout).strip().splitlines()[:1]}")
        return None
    return diags


def _find_guard_docstring(lines: list[str], guard_line: int) -> tuple[int, int] | None:
    """Locate the `/-- … -/` docstring attached to `#guard_msgs` (1-based `guard_line`).

    Returns the 0-based, inclusive line range of the comment, or None."""
    i = guard_line - 2  # 0-based index of the line above `#guard_msgs`
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0 or lines[i].strip() != "-/":
        return None
    start = i
    while start >= 0 and not lines[start].lstrip().startswith("/--"):
        start -= 1
    return None if start < 0 else (start, i)


def _squash(s: str) -> str:
    """Drop every whitespace character, so only the pinned content is compared."""
    return "".join(s.split())


def fix_guard_msgs(run: Run, rel: Path) -> bool:
    """Rewrite mismatching `#guard_msgs` docstrings in one file. True if changed."""
    diags = _lean_diagnostics(run, rel)
    if diags is None:
        return False

    guards = sorted(d["pos"]["line"] for d in diags
                    if d.get("severity") == "error" and GUARD_ERR in d.get("data", ""))
    if not guards:
        return False

    # Attribute every other diagnostic to the `#guard_msgs` it belongs to: the
    # guarded command sits below the `#guard_msgs` token, before the next one.
    others = [d for d in diags
              if not (d.get("severity") == "error" and GUARD_MISSING in d.get("data", ""))]
    messages: dict[int, list[str]] = {}
    for idx, gline in enumerate(guards):
        nxt = guards[idx + 1] if idx + 1 < len(guards) else 1 << 30
        owned = sorted((d for d in others if gline <= d["pos"]["line"] < nxt),
                       key=lambda d: (d["pos"]["line"], d["pos"]["column"]))
        if not owned:
            run.notes.append(f"{rel}:{gline}: `#guard_msgs` failed but Lean emitted no "
                             "message to pin; fix by hand")
            continue
        messages[gline] = [
            f"{SEVERITY_PREFIX.get(d.get('severity'), 'info')}: {d.get('data', '').rstrip()}"
            for d in owned]

    if not messages:
        return False

    path = run.root / "backends" / "lean" / rel
    text = run.read(path)
    lines = text.split("\n")
    fixed = 0
    # Patch bottom-up so earlier line numbers stay valid.
    for gline in sorted(messages, reverse=True):
        span = _find_guard_docstring(lines, gline)
        if span is None:
            run.notes.append(f"{rel}:{gline}: could not find the `#guard_msgs` docstring")
            continue
        start, end = span
        message = "\n\n".join(messages[gline])  # `#guard_msgs` separates messages by a blank line

        # This pass exists only to re-flow line breaks. If the pinned content
        # itself changed, the reduced `Error` enum changed what a spec *says* —
        # that is a real difference and a human has to look at it.
        old = "\n".join(lines[start + 1 : end])
        if _squash(old) != _squash(message):
            quote = lambda s: "\n".join("      " + ln for ln in s.strip().split("\n"))
            run.notes.append(
                f"{rel}:{gline}: `#guard_msgs` expectation differs by more than "
                f"whitespace — not rewritten.\n    pinned:\n{quote(old)}\n"
                f"    Lean produced:\n{quote(message)}")
            continue

        lines[start : end + 1] = ["/--"] + message.split("\n") + ["-/"]
        fixed += 1
    if not fixed:
        return False
    run.write(path, text, "\n".join(lines), fixed,
              f"re-wrapped {fixed} `#guard_msgs` expectation(s)")
    return True


def fix_guard_msgs_all(run: Run, explicit: list[str]) -> None:
    lean_dir = run.root / "backends" / "lean"
    if explicit:
        targets = []
        for f in explicit:
            # Accept paths relative to `backends/lean`, to the checkout, or to $PWD.
            cands = [lean_dir / f, run.root / f, Path.cwd() / f, Path(f)]
            hit = next((c for c in cands if c.is_file()), None)
            if hit is None:
                raise PatchError(f"no such Lean file: {f}")
            try:
                targets.append(hit.resolve().relative_to(lean_dir.resolve()))
            except ValueError:
                raise PatchError(f"{f} is not under {lean_dir}")
    else:
        targets, outside = [], []
        for p in lean_files(run.root):
            if "#guard_msgs" not in p.read_text(encoding="utf-8"):
                continue
            if lean_dir in p.parents:
                targets.append(p.relative_to(lean_dir))
            else:
                # `lake env lean` only knows how to elaborate the `backends/lean`
                # project, so say so rather than dropping the file on the floor.
                outside.append(p.relative_to(run.root))
        for rel in outside:
            run.notes.append(f"{rel}: has `#guard_msgs` but lives outside `backends/lean`; "
                             "check it by hand")
    run.log(f"checking {len(targets)} file(s) with `#guard_msgs` expectations")

    # A fix can change another file's expected output, so iterate to a fixpoint.
    pending = targets
    for _round in range(3):
        with ThreadPoolExecutor(max_workers=max(1, (os.cpu_count() or 4) // 2)) as pool:
            changed = list(pool.map(lambda r: (r, fix_guard_msgs(run, r)), pending))
        pending = [r for r, ch in changed if ch]
        if not pending:
            return
    run.notes.append("`#guard_msgs` fixes did not converge after 3 rounds")


# ---------------------------------------------------------------------------
# Pass 6: post-conditions
# ---------------------------------------------------------------------------


def check_leftovers(run: Run) -> list[str]:
    """Report anything that still mentions a removed constructor, or looks wrong."""
    problems: list[str] = []
    if run.check:
        return problems  # nothing was written, leftovers are expected

    for path in lean_files(run.root):
        text = run.read(path)
        rel = path.relative_to(run.root)
        for m in _CTOR_RE.finditer(text):
            line = text[: m.start()].count("\n") + 1
            problems.append(f"{rel}:{line}: leftover `{m.group(1)}`")
        # A `fun | .panic => … | .panic => …` would compile to dead code.
        for m in _FUN_MATCH_RE.finditer(text):
            try:
                close = _matching_paren(text, m.start())
            except PatchError:
                continue
            arms = _split_arms(text[m.start() + len("(fun") : close])
            if not arms:
                continue
            pats = [p for p, _ in arms if p != "_"]
            if len(pats) != len(set(pats)):
                line = text[: m.start()].count("\n") + 1
                problems.append(f"{rel}:{line}: duplicate arm(s) in an `Error` match: {pats}")

    # Outside the Lean sources nothing should mention these names. `.lake` holds
    # gigabytes of dependencies, so prune it rather than walking into it. The
    # fork's patch descriptions and scripts (`fork/`) name the removed
    # constructors on purpose.
    suffixes = {".ml", ".mli", ".md", ".rs", ".py", ".sh", ".txt", ".yml", ".yaml"}
    for dirpath, dirnames, filenames in os.walk(run.root):
        dirnames[:] = [d for d in dirnames if d not in {".git", ".lake", "_build", "target"}
                       and not (Path(dirpath) == run.root and d == "fork")]
        for name in filenames:
            path = Path(dirpath) / name
            if path.suffix not in suffixes:
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                continue
            for m in _CTOR_RE.finditer(text):
                line = text[: m.start()].count("\n") + 1
                problems.append(f"{path.relative_to(run.root)}:{line}: mentions "
                                f"`{m.group(1)}` (outside the Lean sources; review by hand)")
    return problems


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if not a.startswith("--")]
    flags = {a for a in argv[1:] if a.startswith("--")}
    unknown = flags - {"--check", "--quiet", "--fix-guard-msgs"}
    if unknown:
        sys.exit(__doc__)
    guard_mode = "--fix-guard-msgs" in flags

    # In --fix-guard-msgs mode the first positional may be the checkout, the rest
    # are Lean files; otherwise there is at most one positional.
    if guard_mode:
        root_arg = args[0] if args and (Path(args[0]) / PRIMITIVES).is_file() else None
        targets = args[1:] if root_arg else args
    else:
        if len(args) > 1:
            sys.exit(__doc__)
        root_arg, targets = (args[0] if args else None), []

    root = find_root(root_arg)
    run = Run(root=root, check="--check" in flags, quiet="--quiet" in flags)
    run.log(f"aeneas checkout: {root}")

    try:
        if guard_mode:
            if run.check:
                sys.exit("error: --fix-guard-msgs cannot be combined with --check")
            fix_guard_msgs_all(run, targets)
            problems: list[str] = []
        else:
            run.log(f"folding {', '.join(REMOVED)} into `panic`"
                    f"{' (dry run)' if run.check else ''}")
            shrink_inductive(run)
            rewrite_error_pred_eq_disj(run)
            files = lean_files(root)
            for path in files:
                merge_colliding_arms(run, path)
            for path in files:
                rename_constructors(run, path)
                rewrite_prose(run, path)
            problems = check_leftovers(run)
    except PatchError as e:
        print(f"\nerror: {e}", file=sys.stderr)
        return 2

    total = sum(run.edits.values())
    verb = "would change" if run.check else "changed"
    print(f"\n{verb} {len(run.edits)} file(s), {total} site(s)")
    if not guard_mode and not run.check and run.edits:
        print("next: build `backends/lean`; if `#guard_msgs` expectations fail, re-run "
              "with --fix-guard-msgs")
    problems += run.notes
    if problems:
        print("\nissues that need a human:", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        return 1
    if run.check and not run.edits:
        print("tree is already reduced")
    return 1 if (run.check and run.edits) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))