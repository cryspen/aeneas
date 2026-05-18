#!/usr/bin/env python3
"""
Walker scaffold for Zero-Skip Step 3 (cluster
``recursive_match_arm_scoping``).

Runs ``aeneas-check`` against the ``paper`` and ``demo`` cert JSONs and
verifies that each of the seven decls listed in
``documentation/plans/prompts/zero-skip-step-3-match-arm-prompt.md``
emits an expected body shape (positive substrings) **and** does not
emit the swap-bug shape (negative substrings).

Why a substring scaffold? The full-pipeline rebuild (cert regen ->
RuntimeShim relink -> lean-diff lake build -> runner exec) takes
~30 s per cycle; a substring scaffold runs in <1 s once aeneas-check
is rebuilt, so the inner walker-iteration loop is dominated by Lean
compile time (~30-60 s per Forward.lean edit) rather than test
overhead.

Run from the worktree root::

    cd aeneas-lean-checker && lake build aeneas-check
    python3 aeneas-lean-checker/tests/Walker/match_arm_scaffold.py

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
TMP_OUT = WORKTREE / "/tmp/match-arm-scaffold-out"
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
            # Also stop at `end <namespace>` line.
            end_ns = src.find("\nend ", start, end)
            if end_ns != -1:
                end = end_ns
            return src[start:end]
    return ""


# (fixture, decl_name, must_contain, must_not_contain)
Case = Tuple[str, str, List[str], List[str]]


CASES: List[Case] = [
    # ---- paper::sum ---------------------------------------------------
    # Oracle:
    #   match l with
    #   | List.Cons x tl => let i ← sum tl; x + i
    #   | List.Nil => ok 0#i32
    (
        "paper",
        "sum",
        [
            "List.Cons",
            "List.Nil",
            # Cons arm makes the recursive call on the *tail binder* (not `l`)
            # and adds the head binder.
            "paper.sum",
            "0#i32",
        ],
        [
            # Pre-fix bug: Cons arm collapses to `ok ()`.
            "List.Cons x2 x3 => ok ()",
            "List.Cons x3 x4 => ok ()",
            "List.Cons x4 x5 => ok ()",
            # Pre-fix bug: Nil arm contains the recursive call body
            # referencing the bare scrutinee `l`.
            "List.Nil =>\n    let l_post",
            # The recursive call must NOT pass the scrutinee `l` — it must
            # bind a tail name. The buggy form was `(paper.sum l)`.
            "(paper.sum l)",
        ],
    ),
    # ---- paper::list_nth_mut -----------------------------------------
    (
        "paper",
        "list_nth_mut",
        [
            "List.Cons",
            "List.Nil",
            # The Nil arm must be the panic / non-recursive arm.
            "paper.list_nth_mut",
        ],
        [
            "List.Cons x2 x3 => ok ()",
            "List.Cons x3 x4 => ok ()",
            "List.Cons x4 x5 => ok ()",
            "(paper.list_nth_mut l ",
            # Pre-fix: an unbalanced ok-paren tail.
            "ok l_post_v, fun ret => l)",
        ],
    ),
    # ---- paper::test_nth ----------------------------------------------
    # Cascade decl. Just ensure it elaborates with the corrected calls
    # — i.e., does not reference `list_nth_mut`/`sum` with bogus forms.
    (
        "paper",
        "test_nth",
        [
            "paper.list_nth_mut",
            "paper.sum",
        ],
        [],
    ),
    # ---- demo::list_nth ----------------------------------------------
    (
        "demo",
        "list_nth",
        [
            "CList.CCons",
            "CList.CNil",
            "demo.list_nth",
        ],
        [
            "CList.CCons x3 x4 => ok ()",
            "(demo.list_nth l ",
            # Bug emitted `ok 0#u32` from CNil's slot; the real Nil body
            # is `fail panic`.
            "CList.CNil =>\n    let t0",
        ],
    ),
    # ---- demo::list_nth_mut ------------------------------------------
    (
        "demo",
        "list_nth_mut",
        [
            "CList.CCons",
            "CList.CNil",
            "demo.list_nth_mut",
        ],
        [
            "CList.CCons x3 x4 => ok ()",
            "(demo.list_nth_mut l ",
            "ok l_post_v, fun ret => l)",
        ],
    ),
    # ---- demo::list_tail ---------------------------------------------
    # NB: `list_tail`'s cert *already* has interleaved arm bodies, so the
    # current emit is close — but the audit lists it as broken because of
    # a tuple-comma misplacement in the CNil arm. Capture both.
    (
        "demo",
        "list_tail",
        [
            "CList.CCons",
            "CList.CNil",
            "demo.list_tail",
        ],
        [
            # The buggy tail-comma form.
            "ok l, fun ret => l)",
        ],
    ),
    # ---- demo::i32_id ------------------------------------------------
    # No match-arm here, but the audit lists it under the same cluster:
    # the recursive call is dropped and an unbound `t3` leaks.
    (
        "demo",
        "i32_id",
        [
            "demo.i32_id",
        ],
        [
            "ok t3",
            "ok t4",
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
