#!/usr/bin/env python3
"""
Differential testing: Python re module vs Strata SMT-based regex checker.

Usage:
    python diff_test.py [--lake-exe <path>]

For each test case in the corpus, runs the regex+string pair through both
Python's re module and Strata's DiffTestCore tool, then reports discrepancies
according to the agreed-upon agreement logic.

Agreement logic:
  agree        Python match   + Strata match
               Python noMatch + Strata noMatch
               Python error   + Strata parseError (patternError or unimplemented)

  bug          Python match   + Strata noMatch          (false negative)
               Python noMatch + Strata match            (false positive)
               Python error   + Strata match/noMatch    (Strata accepts invalid regex)
               Python match/noMatch + Strata parseError:patternError
                                                        (Strata rejects valid regex)

  known_gap    Python match/noMatch + Strata parseError:unimplemented
                                                        (feature not yet supported)

  investigate  Strata smtError, or any other combination
"""

import re
import subprocess
import sys
import os
import argparse

# ── Test corpus ────────────────────────────────────────────────────────────────
# Each entry is (python_regex, test_string, mode)
# mode is one of: "match", "fullmatch", "search"

CORPUS = [
    # Simple literals
    ("a",    "a",   "fullmatch"),
    ("a",    "b",   "fullmatch"),
    ("ab",   "ab",  "fullmatch"),
    ("ab",   "a",   "fullmatch"),
    ("ab",   "abc", "fullmatch"),

    # match mode: anchored at start, allows trailing content
    ("a",    "abc", "match"),
    ("a",    "bcd", "match"),
    ("ab",   "abc", "match"),
    ("ab",   "bcd", "match"),

    # Anchors: ^, $, both, neither
    ("^a",   "a",   "fullmatch"),
    ("^a",   "ba",  "fullmatch"),
    ("a$",   "a",   "fullmatch"),
    ("a$",   "ab",  "fullmatch"),
    ("^a$",  "a",   "fullmatch"),
    ("^a$",  "ab",  "fullmatch"),
    ("^a$",  "ba",  "fullmatch"),
    # ^ is a no-op at the start in match mode; $ triggers trailing anchor
    ("^a$",  "a",   "match"),
    ("^a$",  "ab",  "match"),

    # Quantifiers
    ("a*",      "",       "fullmatch"),
    ("a*",      "aaa",    "fullmatch"),
    ("a*",      "b",      "fullmatch"),
    ("a+",      "",       "fullmatch"),
    ("a+",      "a",      "fullmatch"),
    ("a+",      "aaa",    "fullmatch"),
    ("a?",      "",       "fullmatch"),
    ("a?",      "a",      "fullmatch"),
    ("a?",      "aa",     "fullmatch"),
    ("a{2,4}",  "a",      "fullmatch"),
    ("a{2,4}",  "aa",     "fullmatch"),
    ("a{2,4}",  "aaaa",   "fullmatch"),
    ("a{2,4}",  "aaaaa",  "fullmatch"),
    ("a{3}",    "aaa",    "fullmatch"),
    ("a{3}",    "aa",     "fullmatch"),

    # Any character
    (".",    "a",  "fullmatch"),
    (".",    "",   "fullmatch"),
    (".",    "ab", "fullmatch"),
    (".+",   "abc", "fullmatch"),

    # Character classes
    ("[a-z]",   "a",  "fullmatch"),
    ("[a-z]",   "z",  "fullmatch"),
    ("[a-z]",   "A",  "fullmatch"),
    ("[^a-z]",  "A",  "fullmatch"),
    ("[^a-z]",  "a",  "fullmatch"),
    ("[abc]",   "b",  "fullmatch"),
    ("[abc]",   "d",  "fullmatch"),
    ("[a-z]+",  "hello", "fullmatch"),
    ("[a-z]+",  "Hello", "fullmatch"),

    # Alternation
    ("a|b",   "a",  "fullmatch"),
    ("a|b",   "b",  "fullmatch"),
    ("a|b",   "c",  "fullmatch"),
    ("a|b|c", "c",  "fullmatch"),
    ("a|b|c", "d",  "fullmatch"),

    # Groups and repetition
    ("(ab)+",   "ab",    "fullmatch"),
    ("(ab)+",   "abab",  "fullmatch"),
    ("(ab)+",   "aba",   "fullmatch"),
    ("(a|b)+",  "abba",  "fullmatch"),
    ("(a|b)+",  "abbc",  "fullmatch"),

    # Anchors inside groups / alternation
    ("(^a$)|(^b$)",  "a",    "fullmatch"),
    ("(^a$)|(^b$)",  "b",    "fullmatch"),
    ("(^a$)|(^b$)",  "c",    "fullmatch"),
    ("^a$|^$b",      "a",    "fullmatch"),
    ("^a$|^$b",      "",     "fullmatch"),
    ("c(^a|b$)d",    "cad",  "fullmatch"),
    ("c(^a|b$)d",    "cbd",  "fullmatch"),
    ("c(^a|b$)d",    "ccd",  "fullmatch"),
    ("(^a|b$)(^c|d$)", "ac", "fullmatch"),
    ("(^a|b$)(^c|d$)", "bd", "fullmatch"),
    ("(^a|b$)(^c|d$)", "bc", "fullmatch"),

    # Dot-star patterns in match mode
    ("a.*b",  "axyzb", "match"),
    ("a.*b",  "ab",    "match"),
    ("a.*b",  "axyz",  "match"),
    ("a.*b",  "baxyzb","match"),

    # search mode
    ("a",    "xax",  "search"),
    ("a",    "xyz",  "search"),
    ("^a$",  "a",    "search"),
    ("^a$",  "xa",   "search"),
    ("^a$",  "ax",   "search"),

    # ok_chars-style pattern
    (r"[a-z0-9.\-]{1,10}",  "test-str-1", "fullmatch"),
    (r"[a-z0-9.\-]{1,10}",  "test-str!",  "fullmatch"),
    (r"[a-z0-9.\-]{1,10}",  "",           "fullmatch"),
    (r"[a-z0-9.\-]{1,10}",  "0123456789a","fullmatch"),

    # Complement / negated char class
    (r"[^b]",    "a",  "fullmatch"),
    (r"[^b]",    "b",  "fullmatch"),
    (r"[^A-Z]+", "hello", "fullmatch"),
    (r"[^A-Z]+", "Hello", "fullmatch"),

    # Empty alternatives / edge cases
    ("",       "",   "fullmatch"),
    ("",       "a",  "fullmatch"),

    # Invalid regexes → Python raises re.error, Strata should give parseError
    ("x{100,2}",  "x",    "fullmatch"),   # invalid bounds
    ("(abc",      "abc",  "fullmatch"),   # unmatched paren
    ("a**",       "a",    "fullmatch"),   # nothing to repeat

    # Unimplemented in Strata (lookahead / lookbehind)
    (r"a(?=b)",   "ab",  "match"),
    (r"a(?!b)",   "ac",  "match"),
    (r"(?<=a)b",  "ab",  "match"),
    (r"(?<!a)b",  "cb",  "match"),
]

# ── Python oracle ──────────────────────────────────────────────────────────────

def run_python(regex: str, string: str, mode: str) -> str:
    """Returns 'match', 'noMatch', or 'error:<msg>'."""
    fn = {"match": re.match, "fullmatch": re.fullmatch, "search": re.search}[mode]
    try:
        return "match" if fn(regex, string) is not None else "noMatch"
    except re.error as e:
        return f"error:{e}"

# ── Strata oracle ──────────────────────────────────────────────────────────────

# Path to the project root, inferred from this script's location.
# Script is at StrataTest/Languages/Python/Regex/diff_test.py, so root is 4 dirs up.
_SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
_PROJECT_ROOT = os.path.abspath(os.path.join(_SCRIPT_DIR, "..", "..", "..", ".."))


def run_strata(cases: list[tuple[str, str, str]], lake_exe: str) -> dict:
    """
    Pipes all test cases to DiffTestCore in one subprocess call.
    Returns a dict keyed by (regex, string, mode) → result string.
    """
    stdin_data = "".join(f"{r}\t{s}\t{m}\n" for r, s, m in cases)
    proc = subprocess.run(
        [lake_exe, "exe", "DiffTestCore"],
        input=stdin_data,
        capture_output=True,
        text=True,
        cwd=_PROJECT_ROOT,
    )
    results = {}
    for line in proc.stdout.splitlines():
        parts = line.split("\t", 3)
        if len(parts) == 4:
            regex, string, mode, result = parts
            results[(regex, string, mode)] = result
        else:
            print(f"  [WARNING] unexpected DiffTestCore output: {line!r}",
                  file=sys.stderr)
    if proc.returncode != 0 and proc.stderr:
        print(f"[DiffTestCore stderr]\n{proc.stderr}", file=sys.stderr)
    return results

# ── Agreement logic ────────────────────────────────────────────────────────────

def classify(py_result: str, st_result: str) -> str:
    """
    Returns one of: 'agree', 'bug', 'known_gap', 'investigate'.
    """
    py_match   = (py_result == "match")
    py_nomatch = (py_result == "noMatch")
    py_error   = py_result.startswith("error:")

    st_match         = (st_result == "match")
    st_nomatch       = (st_result == "noMatch")
    st_pattern_error = (st_result == "parseError:patternError")
    st_unimpl        = (st_result == "parseError:unimplemented")
    st_parse_error   = st_pattern_error or st_unimpl
    st_smt_error     = st_result.startswith("smtError:")

    # Agreement
    if py_match   and st_match:        return "agree"
    if py_nomatch and st_nomatch:      return "agree"
    if py_error   and st_parse_error:  return "agree"

    # Bugs
    if py_match   and st_nomatch:                    return "bug"
    if py_nomatch and st_match:                      return "bug"
    if py_error   and (st_match or st_nomatch):      return "bug"  # Strata accepted an invalid regex
    if (py_match or py_nomatch) and st_pattern_error: return "bug"  # Strata rejected a valid regex

    # Known gap: Strata says unimplemented for a regex Python accepts
    if (py_match or py_nomatch) and st_unimpl:       return "known_gap"

    # Anything else (smtError, missing output, etc.)
    return "investigate"

# ── Driver ─────────────────────────────────────────────────────────────────────

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Differential regex test: Python re module vs Strata SMT backend"
    )
    parser.add_argument(
        "--lake-exe", default="lake",
        help="Path to the lake executable (default: lake)"
    )
    args = parser.parse_args()

    print(f"Running {len(CORPUS)} test cases against Strata (project root: {_PROJECT_ROOT})...")

    strata_results = run_strata(CORPUS, args.lake_exe)

    counts: dict[str, int] = {"agree": 0, "bug": 0, "known_gap": 0, "investigate": 0}
    bugs, gaps, investigations = [], [], []

    for (regex, string, mode) in CORPUS:
        py  = run_python(regex, string, mode)
        st  = strata_results.get((regex, string, mode), "smtError:missing_output")
        verdict = classify(py, st)
        counts[verdict] += 1
        entry = (regex, string, mode, py, st)
        if verdict == "bug":
            bugs.append(entry)
        elif verdict == "known_gap":
            gaps.append(entry)
        elif verdict == "investigate":
            investigations.append(entry)

    # ── Report ─────────────────────────────────────────────────────────────────
    print(f"\n{'─' * 62}")
    print(f"  agree: {counts['agree']:3}   bugs: {counts['bug']:3}   "
          f"known gaps: {counts['known_gap']:3}   investigate: {counts['investigate']:3}")
    print(f"{'─' * 62}")

    if bugs:
        print(f"\n🐛  BUGS ({len(bugs)}) — Strata and Python disagree on a valid regex:")
        for regex, string, mode, py, st in bugs:
            print(f"  regex={regex!r}  string={string!r}  mode={mode!r}")
            print(f"    Python : {py}")
            print(f"    Strata : {st}")

    if gaps:
        print(f"\n⚠️   KNOWN GAPS ({len(gaps)}) — Strata says 'unimplemented':")
        for regex, string, mode, py, st in gaps:
            print(f"  regex={regex!r}  string={string!r}  mode={mode!r}  python={py}")

    if investigations:
        print(f"\n🔍  INVESTIGATE ({len(investigations)}):")
        for regex, string, mode, py, st in investigations:
            print(f"  regex={regex!r}  string={string!r}  mode={mode!r}")
            print(f"    Python : {py}")
            print(f"    Strata : {st}")

    if not bugs and not investigations:
        print("\n✅  All cases either agree or are known gaps.")

    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
