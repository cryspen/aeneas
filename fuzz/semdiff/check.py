#!/usr/bin/env python3
"""check.py -- join native ground truth with Lean verdicts, emit per-test result.

Inputs:
  NATIVE.json : array of {name,status,kind,msg} from native_run.sh
                status in {OK,PANIC}; kind in
                {ok,assertionFailure,integerOverflow,divisionByZero,
                 arrayOutOfBounds,panic}
  LEAN.txt    : lines `SEMDIFF|<name>|<status>` from the Lean driver
                status in {OK, FAIL:<variant>, DIV}

Verdicts (per test):
  MATCH            native and Lean agree on OK-vs-FAIL (and, in --strict, on
                   the failure kind too)
  MISMATCH         hard semantic divergence -- the bug signal:
                     native OK  but Lean FAIL   (Lean over-rejects), or
                     native FAIL but Lean OK    (Lean misses a panic)
  MISMATCH_KIND    both fail but disagree on the error kind (only surfaced in
                   --strict; a weaker signal, often a modelling nuance)
  INCONCLUSIVE_DIV Lean evaluation diverges (`.div`) -- cannot compare
  LEAN_INCONCLUSIVE  a Lean def was emitted for this test but `#eval` produced
                     no verdict -- almost always because the function is
                     `noncomputable` (e.g. a range-`for` loop, whose
                     core::iter::range::Step methods Aeneas emits as `axiom`s).
                     Requires --expected to distinguish from MISSING_LEAN.
  MISSING_NATIVE / MISSING_LEAN  test present on only one side (no Lean def
                     emitted at all, e.g. the fn took arguments)

Exit code: 0 if no MISMATCH (and, in --strict, no MISMATCH_KIND); else 1.
Prints a JSON report to stdout and a human summary to stderr.
"""
import argparse
import json
import sys

# Map native panic kind -> Lean Error variant name.
NATIVE_TO_LEAN = {
    "assertionFailure": "assertionFailure",
    "integerOverflow": "integerOverflow",
    "divisionByZero": "divisionByZero",
    "arrayOutOfBounds": "arrayOutOfBounds",
    "panic": "panic",
}


def parse_lean(path):
    out = {}
    for line in open(path):
        line = line.strip()
        if not line.startswith("SEMDIFF|"):
            continue
        _, name, status = line.split("|", 2)
        out[name] = status
    return out


def native_outcome(entry):
    if entry["status"] == "OK":
        return ("OK", None)
    return ("FAIL", entry.get("kind", "panic"))


def lean_outcome(status):
    if status == "OK":
        return ("OK", None)
    if status == "DIV":
        return ("DIV", None)
    if status.startswith("FAIL:"):
        return ("FAIL", status[len("FAIL:"):])
    return ("FAIL", "panic")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("native_json")
    ap.add_argument("lean_txt")
    ap.add_argument("--strict", action="store_true",
                    help="also require the failure KIND to match")
    ap.add_argument("--expected", default=None,
                    help="file whose first line is 'tests: n1 n2 ...' (the defs "
                         "gen_driver emitted); lets us tell noncomputable evals "
                         "apart from defs that were never emitted")
    args = ap.parse_args()

    native = {e["name"]: e for e in json.load(open(args.native_json))}
    lean = parse_lean(args.lean_txt)

    expected = None
    if args.expected:
        txt = open(args.expected).read().strip()
        if txt.startswith("tests:"):
            txt = txt[len("tests:"):]
        expected = set(txt.split())

    names = sorted(set(native) | set(lean))
    report = []
    bad = 0
    counts = {}
    for name in names:
        if name not in native:
            verdict = "MISSING_NATIVE"
        elif name not in lean:
            # A def was emitted but produced no verdict -> noncomputable eval.
            if expected is not None and name in expected:
                verdict = "LEAN_INCONCLUSIVE"
            else:
                verdict = "MISSING_LEAN"
        else:
            no, nk = native_outcome(native[name])
            lo, lk = lean_outcome(lean[name])
            if lo == "DIV":
                verdict = "INCONCLUSIVE_DIV"
            elif no != lo:
                verdict = "MISMATCH"
            else:
                # same OK/FAIL class
                if no == "FAIL" and args.strict:
                    want = NATIVE_TO_LEAN.get(nk, nk)
                    verdict = "MATCH" if want == lk else "MISMATCH_KIND"
                else:
                    verdict = "MATCH"
        counts[verdict] = counts.get(verdict, 0) + 1
        if verdict == "MISMATCH" or (args.strict and verdict == "MISMATCH_KIND"):
            bad += 1
        report.append({
            "name": name,
            "native": native.get(name),
            "lean": lean.get(name),
            "verdict": verdict,
        })

    json.dump(report, sys.stdout, indent=2)
    sys.stdout.write("\n")
    summary = " ".join(f"{k}={v}" for k, v in sorted(counts.items()))
    sys.stderr.write(f"semdiff summary: {summary}\n")
    if bad:
        sys.stderr.write(f"semdiff: {bad} MISMATCH(es) -- semantic divergence found\n")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
