#!/usr/bin/env python3
"""
Walker scaffold for Zero-Skip Step 5 (cluster
``loop_body_undefined_locals``).

Runs ``aeneas-check`` against the ``demo`` cert JSON and verifies that
the ``list_nth1`` / ``list_nth1_loop`` / ``list_nth1_loop.body`` triplet
emits the expected wrapper signature shape and does not emit the
known-bug substrings (undefined ``s33`` / ``t3`` locals, wrong-typed
input ``l : Std.U32``).

Why a substring scaffold? Same rationale as
``match_arm_scaffold.py``: the full-pipeline rebuild
(cert regen -> RuntimeShim relink -> lean-diff lake build) takes
~30 s per cycle; a substring scaffold runs in <1 s once aeneas-check
is rebuilt, so the inner walker-iteration loop is dominated by Lean
compile time (~30-60 s per Loops.lean edit) rather than test
overhead.

Run from the worktree root::

    cd aeneas-lean-checker && lake build aeneas-check
    python3 aeneas-lean-checker/tests/Walker/loop_body_scaffold.py

Exit code 0 iff every assertion passes. On failure, prints the
offending decl, the failing assertion, and the relevant body snippet.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple

WORKTREE = Path(__file__).resolve().parents[3]
AENEAS_CHECK = WORKTREE / "aeneas-lean-checker/.lake/build/bin/aeneas-check"
LLBC_DIR = WORKTREE / "tests/llbc"
TMP_OUT = WORKTREE / "/tmp/loop-body-scaffold-out"
TMP_OUT.mkdir(parents=True, exist_ok=True)


def regen_fixture(fixture: str) -> Path:
    out = TMP_OUT / f"{fixture}.lean"
    res = subprocess.run(
        [str(AENEAS_CHECK), str(LLBC_DIR / f"{fixture}.cert.json"), "--out", str(out)],
        check=False,
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        print(f"FAIL regen {fixture}:\n{res.stderr}")
        sys.exit(2)
    return out


_DEF_HEAD = re.compile(r"^def\s+(\S+)", re.MULTILINE)


def extract_decl_body(src: str, name: str) -> str:
    """Return text of `def {name} ...` up to the next top-level `def`/`end`."""
    matches = list(_DEF_HEAD.finditer(src))
    for i, m in enumerate(matches):
        if m.group(1) == name:
            start = m.start()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(src)
            end_ns = src.find("\nend ", start, end)
            if end_ns != -1:
                end = end_ns
            return src[start:end]
    return ""


# (fixture, decl_name, must_contain, must_not_contain)
Case = Tuple[str, str, List[str], List[str]]


CASES: List[Case] = [
    # ---- demo::list_nth1 (top-level wrapper) -------------------------
    # Oracle:
    #   def list_nth1 {T : Type} (l : CList T) (i : Std.U32) : Result T := do
    #     list_nth1_loop l i
    (
        "demo",
        "list_nth1",
        [
            # Generic param `T` must be (re)introduced on the wrapper.
            "{T : Type}",
            # First input must be `CList T`, not the buggy `Std.U32`.
            "(l : CList T)",
            "(i : Std.U32)",
            ": Result T",
            # The wrapper just calls the loop wrapper.
            "list_nth1_loop l i",
        ],
        [
            # Pre-fix bug: `l` was typed `Std.U32` because the loop
            # translator's `tdm` was empty.
            "(l : Std.U32)",
        ],
    ),
    # ---- demo::list_nth1_loop (loop wrapper) -------------------------
    # Oracle:
    #   def list_nth1_loop {T : Type} (l : CList T) (i : Std.U32) : Result T := do
    #     match l with
    #     | CList.CCons x tl => if i = 0#u32 then ok x else ...
    #     | CList.CNil => fail panic
    #   partial_fixpoint
    (
        "demo",
        "list_nth1_loop",
        [
            "{T : Type}",
            "(l : CList T)",
            "(i : Std.U32)",
            ": Result T",
        ],
        [
            "(l : Std.U32)",
        ],
    ),
    # ---- demo::list_nth1_loop.body (loop body) -----------------------
    # The body's exact shape depends on whether buildLoopBody handles
    # the match-then-branch pattern. At minimum the body must not
    # reference an undefined `s33` (the bare SymVal-id name we leak
    # when the assert's cond isn't resolved against the binop binding)
    # or `t3` (an undefined fresh-name reference).
    (
        "demo",
        "list_nth1_loop.body",
        [
            "{T : Type}",
        ],
        [
            # Pre-fix bugs: bare SymVal id leak.
            "if s33",
            "ok t3",
            # `l : Std.U32` again — same tdm-threading bug applies to
            # the body's emit.
            "(l : Std.U32)",
        ],
    ),
]


def main() -> int:
    src_cache: Dict[str, str] = {}
    failures: List[str] = []
    for fixture, name, mustC, mustNot in CASES:
        if fixture not in src_cache:
            src_cache[fixture] = regen_fixture(fixture).read_text()
        body = extract_decl_body(src_cache[fixture], name)
        if not body:
            failures.append(f"[MISSING] {fixture}::{name}: no `def {name}` in emit")
            continue
        for s in mustC:
            if s not in body:
                failures.append(
                    f"[NOT-PRESENT] {fixture}::{name}: missing required substring {s!r}\n  body:\n{body}"
                )
        for s in mustNot:
            if s in body:
                failures.append(
                    f"[FORBIDDEN] {fixture}::{name}: bug substring {s!r} STILL PRESENT\n  body:\n{body}"
                )

    if failures:
        print(f"\nFAIL ({len(failures)} assertion(s)):\n")
        for f in failures:
            print(f"  {f}\n")
        return 1
    print(f"PASS ({len(CASES)} decls, all assertions satisfied)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
