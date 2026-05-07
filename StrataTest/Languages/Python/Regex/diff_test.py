#!/usr/bin/env python3
"""
Differential testing: Python re module vs Strata SMT-based regex checker.

Usage:
    python diff_test.py [--lake-exe <path>]

For each test case in the corpus, runs the regex+string pair through both
Python's re module and Strata's DiffTestCore tool, then reports discrepancies
according to the agreement logic.

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
# Each entry is (python_regex, test_string, mode).
# mode is one of: "match", "fullmatch", "search".
# Every comment ends with the Python ground-truth answer: # match / # noMatch / # error.

CORPUS = [

    # ── Literals ────────────────────────────────────────────────────────────────

    ("a",    "a",   "fullmatch"),  # match
    ("a",    "b",   "fullmatch"),  # noMatch
    ("ab",   "ab",  "fullmatch"),  # match
    ("ab",   "a",   "fullmatch"),  # noMatch — too short
    ("ab",   "abc", "fullmatch"),  # noMatch — too long

    # match mode: anchored at start, trailing content allowed
    ("a",    "abc", "match"),      # match
    ("a",    "bcd", "match"),      # noMatch — doesn't start with a
    ("ab",   "abc", "match"),      # match
    ("ab",   "bcd", "match"),      # noMatch

    # ── Character atoms ─────────────────────────────────────────────────────────

    # Dot (anychar): matches exactly one character
    (".",    "a",   "fullmatch"),  # match
    (".",    "",    "fullmatch"),  # noMatch — needs exactly one char
    (".",    "ab",  "fullmatch"),  # noMatch — two chars
    (".+",   "abc", "fullmatch"),  # match

    # Character ranges
    ("[a-z]",  "a",     "fullmatch"),  # match
    ("[a-z]",  "z",     "fullmatch"),  # match
    ("[a-z]",  "A",     "fullmatch"),  # noMatch — uppercase
    ("[abc]",  "b",     "fullmatch"),  # match
    ("[abc]",  "d",     "fullmatch"),  # noMatch
    ("[a-z]+", "hello", "fullmatch"),  # match
    ("[a-z]+", "Hello", "fullmatch"),  # noMatch — H is uppercase

    # Negated classes [^...]: complement intersected with allchar
    ("[^a-z]",  "A",     "fullmatch"),  # match
    ("[^a-z]",  "a",     "fullmatch"),  # noMatch
    (r"[^b]",   "a",     "fullmatch"),  # match
    (r"[^b]",   "b",     "fullmatch"),  # noMatch
    (r"[^A-Z]+","hello",  "fullmatch"),  # match
    (r"[^A-Z]+","Hello",  "fullmatch"),  # noMatch — H is uppercase
    # Complement must be single-char, not multi-char or empty
    (r"[^a]",   "",      "fullmatch"),  # noMatch — must be exactly 1 char
    (r"[^a]",   "bc",    "fullmatch"),  # noMatch — 2 chars, not 1
    (r"[^a]",   "bb",    "fullmatch"),  # noMatch — 2 chars
    (r"[^b]+",  "",      "fullmatch"),  # noMatch — below min (1)

    # ── Quantifiers ─────────────────────────────────────────────────────────────

    # * (star): zero or more
    ("a*",     "",      "fullmatch"),  # match
    ("a*",     "aaa",   "fullmatch"),  # match
    ("a*",     "b",     "fullmatch"),  # noMatch

    # + (plus = concat r (star r)): one or more
    ("a+",     "",      "fullmatch"),  # noMatch
    ("a+",     "a",     "fullmatch"),  # match
    ("a+",     "aaa",   "fullmatch"),  # match

    # deeply nested plus — a few cases to verify recursion depth, not re-testing a+ semantics
    ("((((((a+)+)+)+)+)+)+", "a",    "fullmatch"),  # match
    ("((((((a+)+)+)+)+)+)+", "b",    "fullmatch"),  # noMatch
    ("((((((a+)+)+)+)+)+)+", "aab",  "match"),      # match — trailing b ok
    ("((((((a+)+)+)+)+)+)+", "bab",  "search"),     # match — found in middle

    # (a+)* — plus inside star: equivalent to a*
    ("(a+)*",  "",     "fullmatch"),  # match — zero groups
    ("(a+)*",  "a",    "fullmatch"),  # match
    ("(a+)*",  "aaa",  "fullmatch"),  # match
    ("(a+)*",  "b",    "fullmatch"),  # noMatch
    ("(a+)*",  "ab",   "match"),      # match — trailing b ok
    ("(a+)*",  "bab",  "search"),     # match — found in middle

    # (a*)+ — star inside plus: equivalent to a*
    ("(a*)+",  "",     "fullmatch"),  # match — one empty group
    ("(a*)+",  "a",    "fullmatch"),  # match
    ("(a*)+",  "aaa",  "fullmatch"),  # match
    ("(a*)+",  "b",    "fullmatch"),  # noMatch
    ("(a*)+",  "ab",   "match"),      # match — trailing b ok
    ("(a*)+",  "bab",  "search"),     # match — found in middle

    # (a+b+)+ — concat of pluses inside plus
    ("(a+b+)+",  "",      "fullmatch"),  # noMatch
    ("(a+b+)+",  "ab",    "fullmatch"),  # match
    ("(a+b+)+",  "aabb",  "fullmatch"),  # match — two chars each
    ("(a+b+)+",  "abab",  "fullmatch"),  # match — two groups
    ("(a+b+)+",  "a",     "fullmatch"),  # noMatch — no b
    ("(a+b+)+",  "ba",    "fullmatch"),  # noMatch — wrong order
    ("(a+b+)+",  "abx",   "match"),      # match — trailing x ok
    ("(a+b+)+",  "xab",   "search"),     # match — found after x

    # (a+|b+)+ — alternation of pluses inside plus
    ("(a+|b+)+",  "",     "fullmatch"),  # noMatch
    ("(a+|b+)+",  "a",    "fullmatch"),  # match
    ("(a+|b+)+",  "b",    "fullmatch"),  # match
    ("(a+|b+)+",  "aabb", "fullmatch"),  # match — aa then bb
    ("(a+|b+)+",  "abba", "fullmatch"),  # match — a, bb, a
    ("(a+|b+)+",  "c",    "fullmatch"),  # noMatch
    ("(a+|b+)+",  "ac",   "match"),      # match — trailing c ok
    ("(a+|b+)+",  "cab",  "search"),     # match — found after c

    # ? (optional = union empty r): zero or one
    ("a?",     "",      "fullmatch"),  # match
    ("a?",     "a",     "fullmatch"),  # match
    ("a?",     "aa",    "fullmatch"),  # noMatch

    # {n,m} and exact {n}
    ("a{2,4}", "a",     "fullmatch"),  # noMatch — too few
    ("a{2,4}", "aa",    "fullmatch"),  # match
    ("a{2,4}", "aaaa",  "fullmatch"),  # match
    ("a{2,4}", "aaaaa", "fullmatch"),  # noMatch — too many
    ("a{3}",   "aaa",   "fullmatch"),  # match
    ("a{3}",   "aa",    "fullmatch"),  # noMatch

    # Zero and exact counts
    ("a{0}",   "",      "fullmatch"),  # match — 0 reps = empty string
    ("a{0}",   "a",     "fullmatch"),  # noMatch
    ("a{1}",   "a",     "fullmatch"),  # match
    ("a{1}",   "aa",    "fullmatch"),  # noMatch
    ("a{0,1}", "",      "fullmatch"),  # match — same language as a?
    ("a{0,1}", "a",     "fullmatch"),  # match
    ("a{0,1}", "aa",    "fullmatch"),  # noMatch

    # Group loops
    ("(ab){2}",   "abab",    "fullmatch"),  # match
    ("(ab){2}",   "ab",      "fullmatch"),  # noMatch — too few
    ("(ab){2}",   "ababab",  "fullmatch"),  # noMatch — too many
    ("(ab){2,3}", "abab",    "fullmatch"),  # match — 2 reps
    ("(ab){2,3}", "ababab",  "fullmatch"),  # match — 3 reps
    ("(ab){2,3}", "ab",      "fullmatch"),  # noMatch — 1 rep
    ("(ab){2,3}", "abababab","fullmatch"),  # noMatch — 4 reps

    # Multi-char class with loop: ok_chars-style identifier check
    (r"[a-z0-9.\-]{1,10}", "test-str-1",  "fullmatch"),  # match
    (r"[a-z0-9.\-]{1,10}", "test-str!",   "fullmatch"),  # noMatch — ! not in class
    (r"[a-z0-9.\-]{1,10}", "",            "fullmatch"),  # noMatch — below min
    (r"[a-z0-9.\-]{1,10}", "0123456789a", "fullmatch"),  # noMatch — 11 chars, over limit

    # Loops in search mode
    ("a{2}",    "xaax",   "search"),  # match — aa found in middle
    ("a{2}",    "xa",     "search"),  # noMatch — only one a
    ("(ab){2}", "xababx", "search"),  # match
    ("(ab){2}", "xabx",   "search"),  # noMatch — only one ab

    # Anchored loops: ^ and $ alongside {n,m}
    ("^a{3}$",   "aaa",    "fullmatch"),  # match
    ("^a{3}$",   "aa",     "fullmatch"),  # noMatch
    ("^a{3}$",   "aaaa",   "fullmatch"),  # noMatch
    ("^a{2,4}$", "a",      "fullmatch"),  # noMatch
    ("^a{2,4}$", "aa",     "fullmatch"),  # match
    ("^a{2,4}$", "aaaa",   "fullmatch"),  # match
    ("^a{2,4}$", "aaaaa",  "fullmatch"),  # noMatch
    ("^a{3}$",   "aaa",    "match"),      # match — $ blocks trailing content
    ("^a{3}$",   "aaab",   "match"),      # noMatch — $ blocks trailing b
    ("a{3}",     "aaab",   "match"),      # match — no $, trailing b allowed

    # ── Alternation ─────────────────────────────────────────────────────────────

    ("a|b",   "a",  "fullmatch"),  # match
    ("a|b",   "b",  "fullmatch"),  # match
    ("a|b",   "c",  "fullmatch"),  # noMatch
    ("a|b|c", "c",  "fullmatch"),  # match
    ("a|b|c", "d",  "fullmatch"),  # noMatch

    # ── Groups ──────────────────────────────────────────────────────────────────

    ("(ab)+",  "ab",    "fullmatch"),  # match
    ("(ab)+",  "abab",  "fullmatch"),  # match
    ("(ab)+",  "aba",   "fullmatch"),  # noMatch
    ("(a|b)+", "abba",  "fullmatch"),  # match
    ("(a|b)+", "abbc",  "fullmatch"),  # noMatch — c not in [ab]

    # ── Anchors: basic behavior ──────────────────────────────────────────────────

    # fullmatch: ^ and $ are effectively redundant (whole string must match anyway)
    ("^a",   "a",   "fullmatch"),  # match
    ("^a",   "ba",  "fullmatch"),  # noMatch
    ("a$",   "a",   "fullmatch"),  # match
    ("a$",   "ab",  "fullmatch"),  # noMatch
    ("^a$",  "a",   "fullmatch"),  # match
    ("^a$",  "ab",  "fullmatch"),  # noMatch
    ("^a$",  "ba",  "fullmatch"),  # noMatch

    # match mode: ^ is a no-op (match already anchors at start); $ cuts off trailing content
    ("^a",   "a",   "match"),      # match
    ("^a",   "ab",  "match"),      # match — trailing b allowed
    ("^a",   "ba",  "match"),      # noMatch
    ("^a$",  "a",   "match"),      # match
    ("^a$",  "ab",  "match"),      # noMatch — $ blocks trailing b

    # ^$ matches only the empty string, across all modes
    ("^$",   "",    "fullmatch"),  # match
    ("^$",   "a",   "fullmatch"),  # noMatch
    ("^$",   "",    "match"),      # match
    ("^$",   "a",   "match"),      # noMatch
    ("^$",   "",    "search"),     # match
    ("^$",   "a",   "search"),     # noMatch

    # Empty pattern: same language as ^$
    ("",     "",    "fullmatch"),  # match
    ("",     "a",   "fullmatch"),  # noMatch

    # search mode basics
    ("a",    "xax",  "search"),    # match
    ("a",    "xyz",  "search"),    # noMatch
    ("^a$",  "a",    "search"),    # match
    ("^a$",  "xa",   "search"),    # noMatch
    ("^a$",  "ax",   "search"),    # noMatch

    # ^ in search: prevents a free prefix
    ("^a",   "abc",  "search"),    # match
    ("^a",   "xabc", "search"),    # noMatch
    ("^a",   "a",    "search"),    # match

    # $ in search: prevents a free suffix
    ("a$",   "ba",    "search"),   # match
    ("a$",   "ab",    "search"),   # noMatch
    ("a$",   "xyzba", "search"),   # match
    ("a$",   "xyzbax","search"),   # noMatch — a is not at end

    # Alternation with anchors across all modes
    ("^a|b$", "a",     "fullmatch"),  # match — ^a covers "a"
    ("^a|b$", "b",     "fullmatch"),  # match — b$ covers "b"
    ("^a|b$", "ab",    "fullmatch"),  # noMatch — neither "a" nor "b" alone
    ("^a|b$", "a",     "match"),      # match
    ("^a|b$", "b",     "match"),      # match
    ("^a|b$", "ab",    "match"),      # match — ^a fires, b is trailing
    ("^a|b$", "xb",    "match"),      # noMatch
    ("^a|b$", "axyz",  "search"),     # match — ^a fires
    ("^a|b$", "xyzb",  "search"),     # match — b$ fires
    ("^a|b$", "xyzc",  "search"),     # noMatch
    ("^a|b$", "axyzb", "search"),     # match — ^a fires at start

    # Group with both anchors, across all modes
    ("^(a|b)$", "a",  "fullmatch"),  # match
    ("^(a|b)$", "b",  "fullmatch"),  # match
    ("^(a|b)$", "ab", "fullmatch"),  # noMatch
    ("^(a|b)$", "a",  "match"),      # match
    ("^(a|b)$", "b",  "match"),      # match
    ("^(a|b)$", "ab", "match"),      # noMatch — $ prevents trailing b
    ("^(a|b)$", "a",  "search"),     # match
    ("^(a|b)$", "ab", "search"),     # noMatch

    # Anchors inside groups / alternation
    ("(^a$)|(^b$)",    "a",  "fullmatch"),  # match
    ("(^a$)|(^b$)",    "b",  "fullmatch"),  # match
    ("(^a$)|(^b$)",    "c",  "fullmatch"),  # noMatch
    ("^a$|^$b",        "a",  "fullmatch"),  # match — first branch covers "a"
    ("^a$|^$b",        "",   "fullmatch"),  # noMatch — ^$b: ^, $, then b — unmatchable

    # ── Anchors: $ followed by non-consuming suffix (concat | true, false => branch) ──
    #
    # When r1 always consumes and r2 may be empty, $ in r1 can still fire if
    # r2 = "".  Strata splits into: Case 1 (r2 = "", $ fires) | Case 2 (r2 ≠ "").

    # a$.*: a (always-consuming) followed by .* (non-consuming)
    ("a$.*",  "a",    "fullmatch"),  # match — $ fires, .* = ""
    ("a$.*",  "ab",   "fullmatch"),  # noMatch — b after a blocks $
    ("a$.*",  "a",    "match"),      # match
    ("a$.*",  "ab",   "match"),      # noMatch
    ("a$.*",  "ba",   "search"),     # match — a at end, $ fires
    ("a$.*",  "ab",   "search"),     # noMatch

    # $ followed by b* or b?: b*/b? can match "", so $ can still fire
    ("a$b*",  "a",    "fullmatch"),  # match
    ("a$b*",  "ab",   "fullmatch"),  # noMatch
    ("a$b?",  "a",    "fullmatch"),  # match
    ("a$b?",  "ab",   "fullmatch"),  # noMatch

    # $ followed by always-consuming suffix: $ is forced unmatchable (concat | true,true =>)
    ("a$.+",  "a",    "match"),      # noMatch — .+ needs ≥1 char after $
    ("a$.+",  "ab",   "match"),      # noMatch
    ("a$b+",  "a",    "fullmatch"),  # noMatch
    ("a$b+",  "ab",   "fullmatch"),  # noMatch

    # Double $: second is redundant
    ("a$$",   "a",    "match"),      # match
    ("a$$",   "ab",   "match"),      # noMatch

    # $ in match mode: terminates the match, no trailing content allowed
    ("a$",    "a",    "match"),      # match
    ("a$",    "ab",   "match"),      # noMatch — b follows $
    ("a$",    "ba",   "match"),      # noMatch — match anchors at start
    ("a$",    "aab",  "match"),      # noMatch

    # a.*$ in match mode: .* followed by $
    ("a.*$",  "axyz", "match"),      # match
    ("a.*$",  "a",    "match"),      # match — .* = "", $ fires
    ("a.*$",  "b",    "match"),      # noMatch

    # a.*b in match mode: must start with a and reach b; trailing content allowed
    ("a.*b",  "axyzb","match"),      # match
    ("a.*b",  "ab",   "match"),      # match
    ("a.*b",  "axyz", "match"),      # noMatch — never reaches b
    ("a.*b",  "baxyzb","match"),     # noMatch — doesn't start with a

    # Multi-char consuming prefix before $
    ("ab$.*",    "ab",   "fullmatch"),  # match
    ("ab$.*",    "abc",  "fullmatch"),  # noMatch — c after $ blocked
    ("ab$.*",    "ab",   "match"),      # match
    ("ab$.*",    "abc",  "match"),      # noMatch
    ("ab$.*",    "xab",  "search"),     # match — ab at end
    ("ab$.*",    "xabc", "search"),     # noMatch

    # Range prefix before $
    ("[a-z]$.*", "a",    "fullmatch"),  # match
    ("[a-z]$.*", "ab",   "fullmatch"),  # noMatch
    ("[a-z]$.*", "xa",   "search"),     # match — lowercase at end
    ("[a-z]$.*", "xa1",  "search"),     # noMatch — digit at end, not in [a-z]

    # Group prefix before $
    ("(ab)$.*",  "ab",   "fullmatch"),  # match
    ("(ab)$.*",  "abc",  "fullmatch"),  # noMatch
    ("(ab)$.*",  "ab",   "match"),      # match

    # ── Anchors: ^ preceded by non-consuming content (concat | false, true => branch) ─
    #
    # When r1 may be empty and r2 always consumes with ^, Strata splits into:
    # Case 1 (r1 = "", ^ fires at original position) | Case 2 (r1 ≠ "", ^ blocked).

    # .*^a: .* may be empty, so ^ can still fire at position 0
    (".*^a",  "a",    "match"),      # match — .* = "", ^ fires, a matches
    (".*^a",  "ab",   "match"),      # match — .* = "", ^ fires, trailing b ok
    (".*^a",  "ba",   "match"),      # noMatch — no way to make .* empty AND ^ fire at a

    # .*^a in search: dotStar wrapper means ^ must still fire at position 0
    (".*^a",  "a",    "search"),     # match
    (".*^a",  "ba",   "search"),     # noMatch
    (".*^a",  "xa",   "search"),     # noMatch

    # a?(^b): a? non-consuming with content, (^b) always-consuming with ^
    ("a?(^b)", "b",   "fullmatch"),  # match — a? = "", ^ fires, b matches
    ("a?(^b)", "ab",  "fullmatch"),  # noMatch — a? = "a" → ^ past start; a? = "" → b ≠ a
    ("a?(^b)", "b",   "match"),      # match
    ("a?(^b)", "ba",  "match"),      # match — a? = "", ^ fires, b matches, trailing a ok
    ("a?(^b)", "ab",  "match"),      # noMatch

    # a?(^b) in search: core_ft/core_ff have atStart=false; ^ must not fire mid-string
    ("a?(^b)", "b",   "search"),     # match — pos 0: a?="", ^ fires, b matches
    ("a?(^b)", "xb",  "search"),     # noMatch
    ("a?(^b)", "ab",  "search"),     # noMatch
    ("a?(^b)", "xab", "search"),     # noMatch
    ("a?(^b)", "ba",  "search"),     # match — pos 0: a?="", ^ fires, b matches
    ("a?(^b)", "bx",  "search"),     # match — pos 0: a?="", ^ fires, b matches

    # ^?(^b) in search: r1=^? has no non-anchor content → split doesn't fire → simple path.
    # The fix (passing atStart instead of true to r2) matters here: with atStart=false in
    # core_ft/core_ff, ^ in r2 must be blocked even though the split condition was not met.
    ("^?(^b)", "b",   "search"),     # match — pos 0: ^?="", ^ fires, b matches
    ("^?(^b)", "xb",  "search"),     # noMatch — ^ can only fire at pos 0; b≠x
    ("^?(^b)", "ab",  "search"),     # noMatch

    # ── Anchors: concat(false, false) — both sides may be empty ─────────────────
    #
    # When both sides may be empty and r2 contains ^, Strata splits into:
    # Case 1 (r1 = "", ^ fires) | Case 2 (r1 ≠ "", ^ blocked).

    # a?^b: parses as concat(concat(a?,^),b); inner false,false; ^ fires only when a? = ""
    ("a?^b",  "b",   "fullmatch"),  # match — a? = "", ^ fires, b matches
    ("a?^b",  "a",   "fullmatch"),  # noMatch — a? = "" → b ≠ a; a? = "a" → ^ past start
    ("a?^b",  "ab",  "fullmatch"),  # noMatch
    ("a?^b",  "b",   "match"),      # match
    ("a?^b",  "ba",  "match"),      # match — a? = "", ^ fires, trailing a ok
    ("a?^b",  "ab",  "match"),      # noMatch

    # a?^b?: outer concat(a?, concat(^,b?)) — false,false with ^ in r2 and content in r1
    ("a?^b?", "",    "fullmatch"),  # match — a? = "", ^ fires, b? = ""
    ("a?^b?", "b",   "fullmatch"),  # match — a? = "", ^ fires, b? = "b"
    ("a?^b?", "a",   "fullmatch"),  # noMatch — a? = "a" → ^ past start; a? = "" → b? ≠ a
    ("a?^b?", "ab",  "fullmatch"),  # noMatch
    ("a?^b?", "",    "match"),      # match
    ("a?^b?", "b",   "match"),      # match
    ("a?^b?", "a",   "match"),      # match — a? = "", ^ fires, b? = "", trailing a ok

    # $ in the middle with always-consuming suffix: unmatchable
    ("a$b",   "ab",  "match"),      # noMatch

    # ── Anchors: inside quantified expressions ───────────────────────────────────
    #
    # For star/loop, Strata splits the iterations into first (atStart), middle
    # (false,false), and last (atEnd) when the inner regex is always-consuming
    # or contains an anchor.

    # (^a)*: ^ only fires for the first iteration; subsequent iterations get atStart=false
    ("(^a)*",     "",    "fullmatch"),  # match — 0 iterations
    ("(^a)*",     "a",   "fullmatch"),  # match — 1 iteration: ^ at 0
    ("(^a)*",     "aa",  "fullmatch"),  # noMatch — 2nd ^ fails at pos 1
    ("(^a)*",     "a",   "match"),      # match — 1 iteration, trailing content allowed
    ("(^a)*",     "aa",  "match"),      # match — 1 iteration enough, trailing a allowed

    # (a$)*: $ only fires for the last iteration; earlier iterations get atEnd=false
    ("(a$)*",     "",    "fullmatch"),  # match — 0 iterations
    ("(a$)*",     "a",   "fullmatch"),  # match — 1 iteration: $ at end
    ("(a$)*",     "aa",  "fullmatch"),  # noMatch — $ after 1st a blocked by 2nd a
    ("(a$)*",     "a",   "match"),      # match
    ("(a$)*",     "ab",  "match"),      # match — 0 iterations match "" at position 0

    # (^a$)*: both anchors — only 1 iteration possible
    ("(^a$)*",    "",    "fullmatch"),  # match — 0 iterations
    ("(^a$)*",    "a",   "fullmatch"),  # match — 1 iteration
    ("(^a$)*",    "aa",  "fullmatch"),  # noMatch — 2 iterations impossible

    # Anchor inside loop: repeated iteration blocked
    ("(^a){2}",   "aa",  "fullmatch"),  # noMatch — 2nd ^ is past start
    ("(^a){2}",   "a",   "fullmatch"),  # noMatch
    ("(a$){2}",   "aa",  "fullmatch"),  # noMatch — $ after 1st a blocks 2nd iteration
    ("(a$){2}",   "a",   "fullmatch"),  # noMatch

    # (^a){0,2}: loop(0,m) with always-consuming anchored inner — first/middle/last split
    ("(^a){0,2}", "",    "fullmatch"),  # match — 0 reps
    ("(^a){0,2}", "a",   "fullmatch"),  # match — 1 rep: ^ at 0
    ("(^a){0,2}", "aa",  "fullmatch"),  # noMatch — 2nd ^ fails at pos 1

    # (a$){0,2}: loop(0,m) with always-consuming anchored inner
    ("(a$){0,2}", "",    "fullmatch"),  # match — 0 reps
    ("(a$){0,2}", "a",   "fullmatch"),  # match — 1 rep: $ at end
    ("(a$){0,2}", "aa",  "fullmatch"),  # noMatch — $ blocked

    # {n,m} with n≥1: recursed via concat; anchor handling falls to concat cases
    ("(^a){1,2}", "a",   "fullmatch"),  # match — 1 rep: ^ at 0
    ("(^a){1,2}", "aa",  "fullmatch"),  # noMatch — 2nd ^ fails at pos 1
    ("(a$){1,2}", "a",   "fullmatch"),  # match — 1 rep: $ at end
    ("(a$){1,2}", "aa",  "fullmatch"),  # noMatch — $ blocked

    # star with non-consuming inner — simple path (no anchor split needed)
    ("(a?)*",     "",    "fullmatch"),  # match
    ("(a?)*",     "a",   "fullmatch"),  # match
    ("(a?)*",     "aaa", "fullmatch"),  # match

    # star with anchored non-consuming inner — split still required
    ("(^a?)*",    "",    "fullmatch"),  # match — 0 iterations
    ("(^a?)*",    "a",   "fullmatch"),  # match — 1 iter: ^ fires, a? = "a"
    ("(^a?)*",    "aa",  "fullmatch"),  # noMatch — ^ fails at pos 1
    ("(a?$)*",    "",    "fullmatch"),  # match — 0 iterations
    ("(a?$)*",    "a",   "fullmatch"),  # match — 1 iter: a? = "a", $ at end
    ("(a?$)*",    "aa",  "fullmatch"),  # noMatch — $ after 1st a blocked

    # loop(0,m) with non-consuming inner — simple path
    ("(a?){0,2}", "",    "fullmatch"),  # match
    ("(a?){0,2}", "a",   "fullmatch"),  # match
    ("(a?){0,2}", "aa",  "fullmatch"),  # match
    ("(a?){0,2}", "aaa", "fullmatch"),  # noMatch — exceeds max

    # loop(0,m) with anchored non-consuming inner — split required
    ("(^a?){0,2}", "",   "fullmatch"),  # match — 0 reps
    ("(^a?){0,2}", "a",  "fullmatch"),  # match — 1 rep: ^ fires, a? = "a"
    ("(^a?){0,2}", "aa", "fullmatch"),  # noMatch — ^ fails at pos 1
    ("(a?$){0,2}", "",   "fullmatch"),  # match — 0 reps
    ("(a?$){0,2}", "a",  "fullmatch"),  # match — 1 rep: a? = "a", $ at end
    ("(a?$){0,2}", "aa", "fullmatch"),  # noMatch — $ blocked

    # ── Anchors: unusual / unmatchable positions ─────────────────────────────────

    # ^ after an always-consuming prefix: ^ is past the start
    ("x(^a)",    "xa",  "fullmatch"),  # noMatch — ^ after x: past start
    ("x(^a)",    "a",   "fullmatch"),  # noMatch
    ("x(^a|b)",  "xb",  "fullmatch"),  # match — ^a fails, b branch works
    ("x(^a|b)",  "xa",  "fullmatch"),  # noMatch — ^a fails, b ≠ a

    # $ blocked by following content
    ("(a$)b",    "ab",  "fullmatch"),  # noMatch — $ before b is unmatchable
    ("(a$)(b)",  "ab",  "fullmatch"),  # noMatch
    ("(a$)b",    "ab",  "match"),      # noMatch

    # Alternation where one branch has a context-killed anchor
    ("(a$|b)c",  "ac",  "fullmatch"),  # noMatch — a$ then c: $ blocked; b ≠ a
    ("(a$|b)c",  "bc",  "fullmatch"),  # match — b branch works
    ("(a$|b)c",  "abc", "fullmatch"),  # noMatch
    ("(a|b$)c",  "ac",  "fullmatch"),  # match — a branch works
    ("(a|b$)c",  "bc",  "fullmatch"),  # noMatch — b$c: $ before c → unmatchable

    # Two anchors that cannot both fire
    ("(^a)(^b)", "ab",  "fullmatch"),  # noMatch — 2nd ^ is past start
    ("(^a)(^b)", "a",   "fullmatch"),  # noMatch
    ("(a$)(b$)", "ab",  "fullmatch"),  # noMatch — 1st $ requires end but b follows
    ("(a$)(b$)", "a",   "fullmatch"),  # noMatch

    # ^ or $ at a position where it can't fire cleanly
    ("(^|$)c",   "c",   "fullmatch"),  # match — ^ fires → "c" matches
    ("(^|$)c",   "xc",  "fullmatch"),  # noMatch — neither fires
    ("a(^|$)b",  "ab",  "fullmatch"),  # noMatch — after a: ^ past start, $ blocked by b

    # Anchors blocked by surrounding always-consuming chars
    ("c(^a|b$)d", "cad", "fullmatch"),  # noMatch
    ("c(^a|b$)d", "cbd", "fullmatch"),  # noMatch
    ("c(^a|b$)d", "ccd", "fullmatch"),  # noMatch
    ("(^a|b$)(^c|d$)", "ac", "fullmatch"),  # noMatch
    ("(^a|b$)(^c|d$)", "bd", "fullmatch"),  # noMatch
    ("(^a|b$)(^c|d$)", "bc", "fullmatch"),  # noMatch

    # Search mode: anchor inside group restricts positional freedom
    ("(^a)(b)",  "ab",  "search"),     # match — ^a forces start
    ("(^a)(b)",  "xab", "search"),     # noMatch — ^ blocks
    ("(a)(b$)",  "ab",  "search"),     # match — b$ forces end
    ("(a)(b$)",  "abx", "search"),     # noMatch — $ blocked by x
    ("(^a)(b$)", "ab",  "search"),     # match — both anchors: exactly "ab"
    ("(^a)(b$)", "xab", "search"),     # noMatch — ^ blocks
    ("(^a)(b$)", "abx", "search"),     # noMatch — $ blocks

    # Match mode: $ inside group cuts off trailing content
    ("(a$|b)c",  "bc",  "match"),      # match
    ("(a$|b)c",  "bcd", "match"),      # match — trailing d allowed

    # ── $ in (false,false) concat — atEnd case-split ────────────────────────────
    #
    # a?$b?: both sides may be empty. $ in r1 should only fire when r2="".
    # Without the atEnd split, $ fires even when b? matches non-empty.
    # The split fires at the inner concat($, b?) level.

    ("a?$b?", "",   "fullmatch"),  # match — a?="", $ fires, b?=""
    ("a?$b?", "a",  "fullmatch"),  # match — a?="a", $ fires, b?=""
    ("a?$b?", "b",  "fullmatch"),  # noMatch — $ at pos 0 but string non-empty; no valid split
    ("a?$b?", "ab", "fullmatch"),  # noMatch — $ can't fire: b? non-empty after $
    ("a?$b?", "",   "match"),      # match
    ("a?$b?", "a",  "match"),      # match
    ("a?$b?", "b",  "match"),      # noMatch
    ("a?$b?", "ab", "match"),      # noMatch — $ can't fire with b? non-empty
    ("a?$b?", "a",  "search"),     # match — pos 1: a?="", $ fires at end, b?=""
    ("a?$b?", "b",  "search"),     # match — pos 1: a?="", $ fires at end, b?=""
    ("a?$b?", "xb", "search"),     # match — pos 2: $ fires at end of string
    ("a?$b?", "ab", "search"),     # match — pos 2: $ fires at end of string

    # (a?$)b?: semantically identical to a?$b? but the $-split fires at the outer
    # concat level (r1=group(a?$) contains $, r2=b? has non-anchor content), exercising
    # the false,false $-split path at a different point in the tree.
    ("(a?$)b?", "",   "fullmatch"),  # match — group matches "", $ fires, b?=""
    ("(a?$)b?", "a",  "fullmatch"),  # match — group matches "a", $ fires, b?=""
    ("(a?$)b?", "ab", "fullmatch"),  # noMatch — $ blocked by non-empty b?
    ("(a?$)b?", "b",  "fullmatch"),  # noMatch — group can't match at end with "b" remaining

    # ── Multi-char literals and patterns ─────────────────────────────────────────

    # Basic multi-char literals
    ("abc",      "abc",    "fullmatch"),  # match
    ("abc",      "ab",     "fullmatch"),  # noMatch — too short
    ("abc",      "abcd",   "fullmatch"),  # noMatch — too long
    ("abc",      "ABC",    "fullmatch"),  # noMatch — case mismatch
    ("abc",      "abc",    "match"),      # match
    ("abc",      "abcd",   "match"),      # match — trailing d allowed
    ("abc",      "xabc",   "match"),      # noMatch — doesn't start with a
    ("abc",      "xabc",   "search"),     # match — found in middle
    ("abc",      "xabcx",  "search"),     # match
    ("abc",      "xabx",   "search"),     # noMatch — no abc substring

    # Multi-char alternation
    ("abc|def",  "abc",    "fullmatch"),  # match
    ("abc|def",  "def",    "fullmatch"),  # match
    ("abc|def",  "abcdef", "fullmatch"),  # noMatch — too long
    ("abc|def",  "abd",    "fullmatch"),  # noMatch
    ("abc|def",  "xdef",   "search"),     # match
    ("abc|def",  "xabx",   "search"),     # noMatch

    # Multi-char groups with quantifiers
    ("(abc)+",   "abc",    "fullmatch"),  # match
    ("(abc)+",   "abcabc", "fullmatch"),  # match
    ("(abc)+",   "abcab",  "fullmatch"),  # noMatch — incomplete last rep
    ("(abc){2}", "abcabc", "fullmatch"),  # match
    ("(abc){2}", "abc",    "fullmatch"),  # noMatch — only 1 rep
    ("(abc){2}", "abcabcabc", "fullmatch"),  # noMatch — 3 reps
    ("(abc){1,3}", "abc",       "fullmatch"),  # match — 1 rep
    ("(abc){1,3}", "abcabcabc", "fullmatch"),  # match — 3 reps
    ("(abc){1,3}", "abcabcabcabc", "fullmatch"),  # noMatch — 4 reps

    # Multi-char alternation inside groups
    ("(ab|cd)+",  "abcd",   "fullmatch"),  # match — ab then cd
    ("(ab|cd)+",  "cdab",   "fullmatch"),  # match — cd then ab
    ("(ab|cd)+",  "abce",   "fullmatch"),  # noMatch — ce not in group
    ("(ab|cd)+",  "xabcdy", "search"),     # match
    ("(ab|cd)+",  "xacx",   "search"),     # noMatch

    # Multi-char character class sequences
    ("[a-z][0-9]",    "a1",    "fullmatch"),  # match
    ("[a-z][0-9]",    "a12",   "fullmatch"),  # noMatch — too long
    ("[a-z][0-9]",    "11",    "fullmatch"),  # noMatch — first char not [a-z]
    ("[a-z][0-9]+",   "a123",  "fullmatch"),  # match
    ("[a-z][0-9]+",   "a",     "fullmatch"),  # noMatch — no digit
    ("[a-z]{2}[0-9]{2}", "ab12", "fullmatch"),  # match
    ("[a-z]{2}[0-9]{2}", "a12",  "fullmatch"),  # noMatch — only 1 letter
    ("[a-z]{2}[0-9]{2}", "ab1",  "fullmatch"),  # noMatch — only 1 digit
    ("[a-z]{2}[0-9]{2}", "xab12y", "search"),   # match
    ("[a-z]{2}[0-9]{2}", "xab1y",  "search"),   # noMatch

    # Multi-char patterns with anchors
    ("^abc$",     "abc",    "fullmatch"),  # match
    ("^abc$",     "xabc",   "fullmatch"),  # noMatch
    ("^abc$",     "abcx",   "fullmatch"),  # noMatch
    ("^abc",      "abcxyz", "search"),     # match — ^ forces start
    ("^abc",      "xabc",   "search"),     # noMatch — ^ blocks
    ("abc$",      "xyzabc", "search"),     # match — $ forces end
    ("abc$",      "abcx",   "search"),     # noMatch — $ blocked by x
    ("^abc$",     "abc",    "search"),     # match — both anchors: exactly "abc"
    ("^abc$",     "xabc",   "search"),     # noMatch
    ("^abc$",     "abcx",   "search"),     # noMatch

    # Multi-char with .* wildcard
    ("abc.*def",  "abcdef",    "fullmatch"),  # match — .* = ""
    ("abc.*def",  "abcXXdef",  "fullmatch"),  # match — .* = "XX"
    ("abc.*def",  "abcdef",    "search"),     # match
    ("abc.*def",  "xabcXXdefy","search"),     # match
    ("abc.*def",  "abcXXdeg",  "fullmatch"),  # noMatch — ends with g not f
    ("abc.+def",  "abcdef",    "fullmatch"),  # noMatch — .+ needs ≥1 char between
    ("abc.+def",  "abcXdef",   "fullmatch"),  # match

    # Multi-char search: overlapping candidates
    ("ab",        "ababab",  "search"),     # match — first ab at pos 0
    ("ab",        "bbbabb",  "search"),     # match — ab at pos 3
    ("ab",        "aabb",    "search"),     # match — ab at pos 1
    ("ab",        "ba",      "search"),     # noMatch — no ab substring
    ("abc",       "aabbc",   "search"),     # noMatch — no abc substring
    ("abc",       "aabcbc",  "search"),     # match — abc at pos 1

    # ── Special characters: colon, backslash, and escaped metacharacters ─────────

    # Literal colon
    ("a:b",       "a:b",    "fullmatch"),  # match
    ("a:b",       "ab",     "fullmatch"),  # noMatch — missing colon
    ("a:b",       "a:b:c",  "fullmatch"),  # noMatch — too long
    ("a:b",       "a:b",    "match"),      # match
    ("a:b",       "a:bc",   "match"),      # match — trailing c allowed
    ("a:b",       "xa:b",   "match"),      # noMatch — doesn't start with a
    ("a:b",       "xa:by",  "search"),     # match
    ("a:b",       "xaby",   "search"),     # noMatch
    ("[a-z]+:[0-9]+", "foo:42",  "fullmatch"),  # match
    ("[a-z]+:[0-9]+", "foo42",   "fullmatch"),  # noMatch — no colon
    ("[a-z]+:[0-9]+", "foo:42",  "match"),      # match
    ("[a-z]+:[0-9]+", "foo:42x", "match"),      # match — trailing x allowed
    ("[a-z]+:[0-9]+", "foo:42",  "search"),     # match
    ("[a-z]+:[0-9]+", "xfoo:42y","search"),     # match
    ("(a:b)+",    "a:b",    "fullmatch"),  # match — 1 rep
    ("(a:b)+",    "a:ba:b", "fullmatch"),  # match — 2 reps
    ("(a:b)+",    "a:ba:",  "fullmatch"),  # noMatch — incomplete last rep
    ("(a:b)+",    "a:b",    "match"),      # match
    ("(a:b)+",    "a:bx",   "match"),      # match — trailing x allowed
    ("^[a-z]+:[0-9]+$", "foo:42",  "fullmatch"),  # match
    ("^[a-z]+:[0-9]+$", "foo:42",  "match"),      # match — $ blocks trailing
    ("^[a-z]+:[0-9]+$", "foo:42x", "match"),      # noMatch — $ blocks x
    ("^[a-z]+:[0-9]+$", "foo:42",  "search"),     # match
    ("^[a-z]+:[0-9]+$", "xfoo:42", "search"),     # noMatch — ^ blocks

    # Escaped metacharacters as literals
    (r"a\.b",    "a.b",    "fullmatch"),  # match — \. matches literal dot
    (r"a\.b",    "axb",    "fullmatch"),  # noMatch — x is not a dot
    (r"a\.b",    "a.b",    "match"),      # match
    (r"a\.b",    "a.bc",   "match"),      # match — trailing c allowed
    (r"a\.b",    "a.b",    "search"),     # match
    (r"a\.b",    "xaxbx",  "search"),     # noMatch
    (r"a\+b",    "a+b",    "fullmatch"),  # match — \+ matches literal +
    (r"a\+b",    "ab",     "fullmatch"),  # noMatch
    (r"a\+b",    "a+b",    "match"),      # match
    (r"a\+b",    "a+bc",   "match"),      # match — trailing c allowed
    (r"a\*b",    "a*b",    "fullmatch"),  # match — \* matches literal *
    (r"a\*b",    "aab",    "fullmatch"),  # noMatch
    (r"a\*b",    "a*b",    "match"),      # match
    (r"a\?b",    "a?b",    "fullmatch"),  # match — \? matches literal ?
    (r"a\?b",    "ab",     "fullmatch"),  # noMatch
    (r"a\?b",    "a?b",    "match"),      # match
    (r"a\(b\)",  "a(b)",   "fullmatch"),  # match — escaped parens are literals
    (r"a\(b\)",  "ab",     "fullmatch"),  # noMatch
    (r"a\(b\)",  "a(b)",   "match"),      # match
    (r"a\[b\]",  "a[b]",   "fullmatch"),  # match — escaped brackets are literals
    (r"a\[b\]",  "ab",     "fullmatch"),  # noMatch
    (r"a\[b\]",  "a[b]",   "match"),      # match
    (r"a\\b",    "a\\b",   "fullmatch"),  # match — \\ matches literal backslash
    (r"a\\b",    "ab",     "fullmatch"),  # noMatch
    (r"a\\b",    "a\\b",   "match"),      # match
    (r"a\\b",    "a\\bc",  "match"),      # match — trailing c allowed
    (r"a\\b",    "xa\\by", "search"),     # match
    (r"a\\b",    "xaby",   "search"),     # noMatch

    # Escaped metacharacter as range start: [\.-z] = range from '.' to 'z'
    (r"[\.-z]+",  "abc",   "fullmatch"),  # match — a,b,c all in range .-z
    (r"[\.-z]+",  "ABC",   "fullmatch"),  # noMatch — A,B,C below '.'
    (r"[\.-z]+",  "-",     "fullmatch"),  # noMatch — '-' (ASCII 45) below '.' (46)
    (r"[\.-z]+",  ".",     "fullmatch"),  # match — '.' is start of range
    (r"[\.-z]+",  "abc",   "search"),     # match

    # Mixed: colon and escaped metacharacters together
    (r"\w+:\d+\.\d+", "foo:3.14",   "fullmatch"),  # match
    (r"\w+:\d+\.\d+", "foo:3x14",   "fullmatch"),  # noMatch — x not a dot
    (r"\w+:\d+\.\d+", "foo:3.14",   "match"),      # match
    (r"\w+:\d+\.\d+", "foo:3.14x",  "match"),      # match — trailing x allowed
    (r"\w+:\d+\.\d+", "xfoo:3.14y", "search"),     # match
    (r"\w+:\d+\.\d+", "xfoo:3x14y", "search"),     # noMatch

    # ── Error cases ──────────────────────────────────────────────────────────────

    ("x{100,2}", "x",   "fullmatch"),  # error — invalid bounds: lo > hi
    ("(abc",     "abc", "fullmatch"),  # error — unmatched parenthesis
    ("a**",      "a",   "fullmatch"),  # error — nothing to repeat

    # ── Unimplemented: lookahead / lookbehind ────────────────────────────────────

    (r"a(?=b)",  "ab",  "match"),      # match
    (r"a(?!b)",  "ac",  "match"),      # match
    (r"(?<=a)b", "ab",  "match"),      # noMatch — re.match at pos 0: nothing precedes b
    (r"(?<!a)b", "cb",  "match"),      # noMatch — re.match at pos 0: char is c, not b

    # ── Unimplemented: non-greedy (lazy) quantifiers ─────────────────────────────

    (r"a*?",  "aaa",   "fullmatch"),  # match — same language as a*
    (r"a*?",  "",      "fullmatch"),  # match
    (r"a+?",  "a",     "fullmatch"),  # match — same language as a+
    (r"a+?",  "aaa",   "fullmatch"),  # match
    (r"a??",  "",      "fullmatch"),  # match — same language as a?
    (r"a??",  "a",     "fullmatch"),  # match
    (r"a*?b", "aaab",  "search"),    # match
    (r"a+?b", "ab",    "search"),    # match

    # ── Unimplemented: \d \w \s shorthand classes ────────────────────────────────

    (r"\d",        "5",      "fullmatch"),  # match
    (r"\d",        "a",      "fullmatch"),  # noMatch
    (r"\d+",       "123",    "fullmatch"),  # match
    (r"\d+",       "12a",    "fullmatch"),  # noMatch
    (r"\D",        "a",      "fullmatch"),  # match
    (r"\D",        "5",      "fullmatch"),  # noMatch
    (r"\w",        "a",      "fullmatch"),  # match
    (r"\w",        "!",      "fullmatch"),  # noMatch
    (r"\w+",       "hello",  "fullmatch"),  # match
    (r"\W",        "!",      "fullmatch"),  # match
    (r"\W",        "a",      "fullmatch"),  # noMatch
    (r"\s",        " ",      "fullmatch"),  # match
    (r"\s",        "a",      "fullmatch"),  # noMatch
    (r"\S",        "a",      "fullmatch"),  # match
    (r"\S",        " ",      "fullmatch"),  # noMatch
    (r"\d+\s\w+",  "42 abc", "fullmatch"),  # match

    # ── Unimplemented: \b \B word-boundary assertions ────────────────────────────

    (r"\bcat\b",  "cat",         "search"),  # match — exact word
    (r"\bcat\b",  "cats",        "search"),  # noMatch — no boundary after t
    (r"\bcat\b",  "the cat now", "search"),  # match — surrounded by spaces
    (r"\bcat\b",  "concatenate", "search"),  # noMatch — cat inside word
    (r"\Bcat\B",  "concatenate", "search"),  # match — non-boundary on both sides

    # ── Unimplemented: \A \Z absolute anchors ────────────────────────────────────

    (r"\Aa",   "abc",  "search"),     # match — \A forces absolute start
    (r"\Aa",   "xabc", "search"),     # noMatch
    (r"a\Z",   "ba",   "search"),     # match — \Z forces absolute end
    (r"a\Z",   "ab",   "search"),     # noMatch
    (r"\Aa\Z", "a",    "fullmatch"),  # match
    (r"\Aa\Z", "ab",   "fullmatch"),  # noMatch

    # ── Unimplemented: non-capturing groups (?:...) ──────────────────────────────

    (r"(?:ab)+",   "abab", "fullmatch"),  # match — same language as (ab)+
    (r"(?:ab)+",   "ab",   "fullmatch"),  # match
    (r"(?:a|b)+",  "abba", "fullmatch"),  # match
    (r"x(?:a|b)y", "xay",  "fullmatch"),  # match
    (r"x(?:a|b)y", "xcy",  "fullmatch"),  # noMatch

    # ── Unimplemented: named groups (?P<name>...) ────────────────────────────────

    (r"(?P<x>a)",         "a",  "fullmatch"),  # match
    (r"(?P<x>a)",         "b",  "fullmatch"),  # noMatch
    (r"(?P<x>a)(?P<y>b)", "ab", "fullmatch"),  # match

    # ── Unimplemented: inline flags (?i) (?m) (?s) ──────────────────────────────

    (r"(?i)hello",  "HELLO", "fullmatch"),  # match — case-insensitive
    (r"(?i)hello",  "Hello", "fullmatch"),  # match
    (r"(?i)hello",  "world", "fullmatch"),  # noMatch
    (r"(?i)[a-z]+", "ABC",   "fullmatch"),  # match
    (r"(?s)a.b",    "axb",   "fullmatch"),  # match — (?s): . also matches \n
    (r"(?m)^a",     "a",     "search"),     # match — (?m): ^ matches per-line

    # ── Unimplemented: backreferences ────────────────────────────────────────────

    (r"(a)\1",   "aa",  "fullmatch"),  # match — group 1 repeated
    (r"(a)\1",   "ab",  "fullmatch"),  # noMatch
    (r"(a|b)\1", "aa",  "fullmatch"),  # match
    (r"(a|b)\1", "bb",  "fullmatch"),  # match
    (r"(a|b)\1", "ab",  "fullmatch"),  # noMatch — mismatch
    (r"(.)\1",   "aa",  "fullmatch"),  # match — any char repeated
    (r"(.)\1",   "ab",  "fullmatch"),  # noMatch
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


def run_strata(cases: list[tuple[str, str, str]], lake_exe: str,
               log_dir: str | None = None) -> dict:
    """
    Pipes all test cases to DiffTestCore in one subprocess call.
    Returns a dict keyed by (regex, string, mode) → result string.
    If log_dir is given, passes --log-dir to DiffTestCore so each generated
    .core.st program is written to <log_dir>/<n>_<mode>.core.st.
    """
    stdin_data = "".join(f"{r}\t{s}\t{m}\n" for r, s, m in cases)
    cmd = [lake_exe, "exe", "DiffTestCore"]
    if log_dir:
        cmd += ["--log-dir", log_dir]
    proc = subprocess.run(
        cmd,
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
    parser.add_argument(
        "--log-dir", default=None, metavar="PATH",
        help="Directory to write generated .core.st programs for debugging"
    )
    args = parser.parse_args()

    print(f"Running {len(CORPUS)} test cases against Strata (project root: {_PROJECT_ROOT})...")
    if args.log_dir:
        print(f"Logging .core.st programs to: {args.log_dir}")

    strata_results = run_strata(CORPUS, args.lake_exe, log_dir=args.log_dir)
    if len(strata_results) != len(CORPUS):
        print(f"ERROR: expected {len(CORPUS)} results from DiffTestCore, got {len(strata_results)}.",
              file=sys.stderr)
        return 2

    counts: dict[str, int] = {"agree": 0, "bug": 0, "known_gap": 0, "investigate": 0}
    bugs, gaps, investigations = [], [], []

    for idx, (regex, string, mode) in enumerate(CORPUS, start=1):
        py  = run_python(regex, string, mode)
        st  = strata_results.get((regex, string, mode), "smtError:missing_output")
        verdict = classify(py, st)
        counts[verdict] += 1
        entry = (idx, regex, string, mode, py, st)
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
        for idx, regex, string, mode, py, st in bugs:
            print(f"  [#{idx}]  regex={regex!r}  string={string!r}  mode={mode!r}")
            print(f"    Python : {py}")
            print(f"    Strata : {st}")

    if gaps:
        print(f"\n⚠️   KNOWN GAPS ({len(gaps)}) — Strata says 'unimplemented':")
        for idx, regex, string, mode, py, st in gaps:
            print(f"  [#{idx}]  regex={regex!r}  string={string!r}  mode={mode!r}  python={py}")

    if investigations:
        print(f"\n🔍  INVESTIGATE ({len(investigations)}):")
        for idx, regex, string, mode, py, st in investigations:
            print(f"  [#{idx}]  regex={regex!r}  string={string!r}  mode={mode!r}")
            print(f"    Python : {py}")
            print(f"    Strata : {st}")

    if not bugs and not investigations:
        print("\n✅  All cases either agree or are known gaps.")

    return 1 if bugs or investigations else 0


if __name__ == "__main__":
    sys.exit(main())
