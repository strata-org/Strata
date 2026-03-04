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

    # ── Anchor stress tests ────────────────────────────────────────────────────

    # $ in match mode: terminates the match, no trailing content allowed
    ("a$",         "a",      "match"),  # match: a at start, then end
    ("a$",         "ab",     "match"),  # no match: b follows $
    ("a$",         "ba",     "match"),  # no match: match anchors start
    ("a$",         "aab",    "match"),  # no match: b follows $
    ("a.*$",       "axyz",   "match"),  # .* before $: consumes to end
    ("a.*$",       "a",      "match"),  # .* matches empty, $ fires
    ("a.*$",       "b",      "match"),  # no match: doesn't start with a
    # a$.* across modes / strings — $ fires, then .* must operate from the end
    ("a$.*",       "a",      "fullmatch"),  # $ fires, .* matches empty → match
    ("a$.*",       "ab",     "fullmatch"),  # $ blocked by b → no match
    ("a$.*",       "a",      "match"),
    ("a$.*",       "ab",     "match"),     # $ blocked → no match
    ("a$.*",       "ba",     "search"),    # a at end: $ fires → match
    ("a$.*",       "ab",     "search"),    # a not at end: $ blocked → no match

    # $ followed by zero-or-more / optional (same root as above)
    ("a$b*",       "a",      "fullmatch"),  # b* matches empty → match
    ("a$b*",       "ab",     "fullmatch"),  # $ blocked by b → no match
    ("a$b?",       "a",      "fullmatch"),  # b? matches empty → match
    ("a$b?",       "ab",     "fullmatch"),  # $ blocked by b → no match

    # $ followed by always-consuming suffix — forces | true,true branch → $ unmatchable
    ("a$.+",       "a",      "match"),     # .+ needs ≥1 char: unmatchable
    ("a$.+",       "ab",     "match"),     # $ blocked regardless
    ("a$b+",       "a",      "fullmatch"), # b+ needs ≥1 b: unmatchable
    ("a$b+",       "ab",     "fullmatch"), # $ blocked regardless

    # double $: second is redundant
    ("a$$",        "a",      "match"),
    ("a$$",        "ab",     "match"),

    # .*^a: .* can match empty → ^ fires at position 0 → 'a' can match
    (".*^a",       "a",      "match"),   # .* = "", ^ fires, a matches
    (".*^a",       "ab",     "match"),   # .* = "", ^ fires, a matches (trailing b ok)
    (".*^a",       "ba",     "match"),   # .* cannot be empty at start (b≠a) → no match

    # .*^a in search: ^ only fires at position 0, so equivalent to ^a in search
    (".*^a",       "a",      "search"),  # ^ fires at start, a matches → match
    (".*^a",       "ba",     "search"),  # a≠b at position 0 → no match
    (".*^a",       "xa",     "search"),  # a≠x at position 0 → no match

    # | true, false => with multi-char r1: concat(a,b) is always-consuming, .* is not
    ("ab$.*",      "ab",     "fullmatch"),  # $ fires, .* matches empty → match
    ("ab$.*",      "abc",    "fullmatch"),  # c after $ → no match
    ("ab$.*",      "ab",     "match"),
    ("ab$.*",      "abc",    "match"),      # c blocks $ → no match
    ("ab$.*",      "xab",    "search"),     # ab at end: $ fires → match
    ("ab$.*",      "xabc",   "search"),     # c after ab: $ blocked → no match

    # | true, false => with range r1
    ("[a-z]$.*",   "a",      "fullmatch"),  # single lowercase: $ fires → match
    ("[a-z]$.*",   "ab",     "fullmatch"),  # b after $ → no match
    ("[a-z]$.*",   "xa",     "search"),     # a at end: $ fires → match
    ("[a-z]$.*",   "xa1",    "search"),     # digit at end, not in [a-z] → no match

    # | true, false => with grouped r1: (ab) wraps the consuming part
    ("(ab)$.*",    "ab",     "fullmatch"),  # $ fires → match
    ("(ab)$.*",    "abc",    "fullmatch"),  # c blocks $ → no match
    ("(ab)$.*",    "ab",     "match"),

    # | false, true =>: r1 non-consuming with content, r2 always-consuming with ^
    # a?(^b): r1=optional(a) [non-consuming, has content], r2=group(concat(^,b)) [always-consuming]
    ("a?(^b)",     "b",      "fullmatch"),  # a?="", ^ fires, b matches → match
    ("a?(^b)",     "ab",     "fullmatch"),  # a?="a" → ^ at pos 1 fails; a?="" → b≠a → no match
    ("a?(^b)",     "b",      "match"),
    ("a?(^b)",     "ba",     "match"),      # a?="", ^ fires, b matches, trailing a ok → match
    ("a?(^b)",     "ab",     "match"),      # no path works → no match

    # | false, false =>: both non-consuming; a?^b parses as concat(concat(a?,^),b)
    # inner concat(a?,^) is false,false; ^ fires only when a? matched empty
    ("a?^b",       "b",      "fullmatch"),  # a?="", ^ fires, b matches → match
    ("a?^b",       "a",      "fullmatch"),  # a?="" → b≠a; a?="a" → ^ at 1 fails → no match
    ("a?^b",       "ab",     "fullmatch"),  # a?="" → b≠a at 0; a?="a" → ^ fails → no match
    ("a?^b",       "b",      "match"),
    ("a?^b",       "ba",     "match"),      # a?="", ^ fires, b matches, trailing a ok → match
    ("a?^b",       "ab",     "match"),      # no path works → no match

    ("a$b",        "ab",     "match"),  # $ in middle: unmatchable

    # ^ in match mode: no-op at start (match already anchors there)
    ("^a",         "a",      "match"),  # match (same as "a" in match mode)
    ("^a",         "ab",     "match"),  # match: trailing b allowed
    ("^a",         "ba",     "match"),  # no match: starts with b

    # ^ and $ in search mode: anchors prevent free prefix/suffix
    ("^a",         "abc",    "search"),  # ^ anchors to start: match
    ("^a",         "xabc",   "search"),  # ^ prevents prefix: no match
    ("^a",         "a",      "search"),  # match
    ("a$",         "ba",     "search"),  # $ anchors to end: match
    ("a$",         "ab",     "search"),  # $ prevents suffix: no match
    ("a$",         "xyzba",  "search"),  # ends with a: match
    ("a$",         "xyzbax", "search"),  # a not at end: no match

    # Alternation with anchors across all modes
    ("^a|b$",      "a",      "fullmatch"),  # ^a covers "a"
    ("^a|b$",      "b",      "fullmatch"),  # b$ covers "b"
    ("^a|b$",      "ab",     "fullmatch"),  # neither: "ab" ≠ "a" and ≠ "b"
    ("^a|b$",      "a",      "match"),  # ^a fires at start, trailing ok
    ("^a|b$",      "b",      "match"),  # b$ fires: "b" ends at $
    ("^a|b$",      "ab",     "match"),  # ^a fires, "b" is trailing
    ("^a|b$",      "xb",     "match"),  # neither fires: x≠a and x≠b
    ("^a|b$",      "axyz",   "search"),  # ^a fires
    ("^a|b$",      "xyzb",   "search"),  # b$ fires
    ("^a|b$",      "xyzc",   "search"),  # neither
    ("^a|b$",      "axyzb",  "search"),  # both fire (^a at start)

    # Group with both anchors
    ("^(a|b)$",    "a",      "fullmatch"),
    ("^(a|b)$",    "b",      "fullmatch"),
    ("^(a|b)$",    "ab",     "fullmatch"),  # no match: length > 1
    ("^(a|b)$",    "a",      "match"),
    ("^(a|b)$",    "b",      "match"),
    ("^(a|b)$",    "ab",     "match"),  # $ prevents trailing b
    ("^(a|b)$",    "a",      "search"),
    ("^(a|b)$",    "ab",     "search"),  # no match: can't be both ^...$ with two chars

    # ^$ (empty-string anchor) in all modes
    ("^$",         "",       "fullmatch"),
    ("^$",         "a",      "fullmatch"),
    ("^$",         "",       "match"),
    ("^$",         "a",      "match"),
    ("^$",         "",       "search"),
    ("^$",         "a",      "search"),

    # Anchors inside a repeated group
    ("(a$)*",      "",       "fullmatch"),  # zero iterations: empty
    ("(a$)*",      "a",      "fullmatch"),  # one iteration at end
    ("(a$)*",      "aa",     "fullmatch"),  # can't iterate twice with $

    # ── Anchors inside groups: unusual / bad-nomatch patterns ─────────────────

    # ^ consumed out of start position → unmatchable branch
    ("x(^a)",          "xa",     "fullmatch"),  # ^ after x: unmatchable
    ("x(^a)",          "a",      "fullmatch"),  # doesn't even start with x
    ("x(^a|b)",        "xb",     "fullmatch"),  # ^a branch fails, b branch saves it
    ("x(^a|b)",        "xa",     "fullmatch"),  # ^a fails, b≠a: no match

    # $ with content still following → unmatchable branch
    ("(a$)b",          "ab",     "fullmatch"),  # looks like "ab" but $ blocks b
    ("(a$)(b)",        "ab",     "fullmatch"),  # same with separate group
    ("(a$)b",          "ab",     "match"),  # same in match mode

    # Alternation: one branch has context-killed anchor
    ("(a$|b)c",        "ac",     "fullmatch"),  # a$ then c: $ blocked; b≠a: no match
    ("(a$|b)c",        "bc",     "fullmatch"),  # b branch works
    ("(a$|b)c",        "abc",    "fullmatch"),  # neither branch matches
    ("(a|b$)c",        "ac",     "fullmatch"),  # a branch works
    ("(a|b$)c",        "bc",     "fullmatch"),  # b$c: $ then c → unmatchable; a≠b: no match

    # Two anchors that cannot both fire
    ("(^a)(^b)",       "ab",     "fullmatch"),  # 2nd ^ is past start: unmatchable
    ("(^a)(^b)",       "a",      "fullmatch"),  # same
    ("(a$)(b$)",       "ab",     "fullmatch"),  # 1st $ requires end but b follows
    ("(a$)(b$)",       "a",      "fullmatch"),  # same

    # ^ or $ at a position where neither fires cleanly
    ("(^|$)c",         "c",      "fullmatch"),  # ^ fires → "c"; $c branch is unmatchable
    ("(^|$)c",         "xc",     "fullmatch"),  # neither fires
    ("a(^|$)b",        "ab",     "fullmatch"),  # after a: ^ past start, $ blocked by b

    # Search mode: anchor inside group restricts positional freedom
    ("(^a)(b)",        "ab",     "search"),  # ^a forces match at start
    ("(^a)(b)",        "xab",    "search"),  # ^ blocks: no match
    ("(a)(b$)",        "ab",     "search"),  # b$ forces match at end
    ("(a)(b$)",        "abx",    "search"),  # $ blocked by x: no match
    ("(^a)(b$)",       "ab",     "search"),  # both anchors: exactly "ab"
    ("(^a)(b$)",       "xab",    "search"),  # ^ blocks
    ("(^a)(b$)",       "abx",    "search"),  # $ blocks

    # Match mode: $ inside group overrides the usual trailing-content allowance
    ("(a$|b)c",        "bc",     "match"),  # b branch + trailing ok
    ("(a$|b)c",        "bcd",    "match"),  # trailing d allowed

    # ── Loop / quantifier edge cases ──────────────────────────────────────────

    # Zero and exact counts
    ("a{0}",           "",       "fullmatch"),  # 0 reps → empty
    ("a{0}",           "a",      "fullmatch"),
    ("a{1}",           "a",      "fullmatch"),
    ("a{1}",           "aa",     "fullmatch"),
    ("a{0,1}",         "",       "fullmatch"),  # same as a?
    ("a{0,1}",         "a",      "fullmatch"),
    ("a{0,1}",         "aa",     "fullmatch"),

    # Group loops
    ("(ab){2}",        "abab",   "fullmatch"),
    ("(ab){2}",        "ab",     "fullmatch"),  # too few
    ("(ab){2}",        "ababab", "fullmatch"),  # too many
    ("(ab){2,3}",      "abab",   "fullmatch"),  # 2 reps: ok
    ("(ab){2,3}",      "ababab", "fullmatch"),  # 3 reps: ok
    ("(ab){2,3}",      "ab",     "fullmatch"),  # 1 rep: no match
    ("(ab){2,3}",      "abababab","fullmatch"),  # 4 reps: no match

    # Anchored loops
    ("^a{3}$",         "aaa",    "fullmatch"),
    ("^a{3}$",         "aa",     "fullmatch"),
    ("^a{3}$",         "aaaa",   "fullmatch"),
    ("^a{2,4}$",       "a",      "fullmatch"),
    ("^a{2,4}$",       "aa",     "fullmatch"),
    ("^a{2,4}$",       "aaaa",   "fullmatch"),
    ("^a{2,4}$",       "aaaaa",  "fullmatch"),
    ("^a{3}$",         "aaa",    "match"),  # $ blocks trailing
    ("^a{3}$",         "aaab",   "match"),  # $ blocks trailing b
    ("a{3}",           "aaab",   "match"),  # no $: trailing b ok

    # Loops in search mode
    ("a{2}",           "xaax",   "search"),  # found in middle
    ("a{2}",           "xa",     "search"),  # only one a: no match
    ("(ab){2}",        "xababx", "search"),
    ("(ab){2}",        "xabx",   "search"),  # only one ab: no match

    # Anchor inside loop: ^ or $ blocks repeated iteration
    ("(^a){2}",        "aa",     "fullmatch"),  # 2nd ^ is past start: unmatchable
    ("(^a){2}",        "a",      "fullmatch"),  # need 2 but ^ blocks 2nd
    ("(a$){2}",        "aa",     "fullmatch"),  # $ after 1st a blocks 2nd iteration
    ("(a$){2}",        "a",      "fullmatch"),  # too few chars regardless

    # ── alwaysConsume branches: star and loop with anchors in inner regex ─────────

    # .star | alwaysConsume=true |: first/middle/last split
    # (^a)*: ^ only fires for the first iteration (middle/last get atStart=false)
    ("(^a)*",      "",      "fullmatch"),  # 0 iterations → match
    ("(^a)*",      "a",     "fullmatch"),  # 1 iteration: ^ at 0, a → match
    ("(^a)*",      "aa",    "fullmatch"),  # 2 iterations: ^ fails at pos 1 → no match
    ("(^a)*",      "a",     "match"),      # 1 iteration (trailing content allowed)
    ("(^a)*",      "aa",    "match"),      # only 1 iter needed, trailing "a" ok → match

    # (a$)*: $ only fires for the last iteration (first/middle get atEnd=false)
    # fullmatch cases already in corpus; add match mode
    ("(a$)*",      "a",     "match"),      # $ fires → no trailing content allowed → match
    ("(a$)*",      "ab",    "match"),      # $ blocks "b" → no match

    # (^a$)*: both anchors — only 1 iteration possible
    ("(^a$)*",     "",      "fullmatch"),  # 0 iterations → match
    ("(^a$)*",     "a",     "fullmatch"),  # 1 iteration → match
    ("(^a$)*",     "aa",    "fullmatch"),  # 2 iterations impossible → no match

    # .loop(0,m) | alwaysConsume=true |: same first/middle/last split
    ("(^a){0,2}",  "",      "fullmatch"),  # 0 reps → match
    ("(^a){0,2}",  "a",     "fullmatch"),  # 1 rep: ^ at 0 → match
    ("(^a){0,2}",  "aa",    "fullmatch"),  # 2 reps: ^ fails at pos 1 → no match
    ("(a$){0,2}",  "",      "fullmatch"),  # 0 reps → match
    ("(a$){0,2}",  "a",     "fullmatch"),  # 1 rep: a, $ at end → match
    ("(a$){0,2}",  "aa",    "fullmatch"),  # 2 reps: $ blocked → no match

    # .loop(n,m) n≥1: recurses via concat (anchor handling falls through to concat fix)
    ("(^a){1,2}",  "a",     "fullmatch"),  # 1 rep: ^ at 0, a → match
    ("(^a){1,2}",  "aa",    "fullmatch"),  # 2 reps: ^ fails at pos 1 → no match
    ("(a$){1,2}",  "a",     "fullmatch"),  # 1 rep: a, $ at end → match
    ("(a$){1,2}",  "aa",    "fullmatch"),  # 2 reps: $ after 1st a blocked → no match

    # .star | alwaysConsume=false |: uses re.*(toCore r1 atStart atEnd) directly
    # No-anchor inner — baseline to confirm branch is reached and works
    ("(a?)*",      "",      "fullmatch"),
    ("(a?)*",      "a",     "fullmatch"),
    ("(a?)*",      "aaa",   "fullmatch"),

    # Anchored non-consuming inner: ^ or $ inside a star that can iterate empty
    ("(^a?)*",     "",      "fullmatch"),  # 0 iterations → match
    ("(^a?)*",     "a",     "fullmatch"),  # 1 iter: ^ fires, a?="a" → match
    ("(^a?)*",     "aa",    "fullmatch"),  # ^ fails at pos 1 → only 1 iter → no match
    ("(a?$)*",     "",      "fullmatch"),  # 0 iterations → match
    ("(a?$)*",     "a",     "fullmatch"),  # 1 iter: a?="a", $ at end → match
    ("(a?$)*",     "aa",    "fullmatch"),  # $ after 1st a blocked by 2nd a → no match

    # .loop(0,m) | alwaysConsume=false |: uses re.loop(r1b, 0, m) directly
    # No-anchor inner — baseline
    ("(a?){0,2}",  "",      "fullmatch"),
    ("(a?){0,2}",  "a",     "fullmatch"),
    ("(a?){0,2}",  "aa",    "fullmatch"),
    ("(a?){0,2}",  "aaa",   "fullmatch"),  # exceeds max → no match

    # Anchored non-consuming inner
    ("(^a?){0,2}", "",      "fullmatch"),  # 0 reps → match
    ("(^a?){0,2}", "a",     "fullmatch"),  # 1 rep: ^ fires, a?="a" → match
    ("(^a?){0,2}", "aa",    "fullmatch"),  # ^ fails at pos 1 → only 1 rep → no match
    ("(a?$){0,2}", "",      "fullmatch"),  # 0 reps → match
    ("(a?$){0,2}", "a",     "fullmatch"),  # 1 rep: a?="a", $ at end → match
    ("(a?$){0,2}", "aa",    "fullmatch"),  # $ after 1st a blocked → no match

    # Invalid regexes → Python raises re.error, Strata should give parseError
    ("x{100,2}",  "x",    "fullmatch"),  # invalid bounds
    ("(abc",      "abc",  "fullmatch"),  # unmatched paren
    ("a**",       "a",    "fullmatch"),  # nothing to repeat

    # Unimplemented in Strata (lookahead / lookbehind)
    (r"a(?=b)",   "ab",  "match"),
    (r"a(?!b)",   "ac",  "match"),
    (r"(?<=a)b",  "ab",  "match"),
    (r"(?<!a)b",  "cb",  "match"),

    # ── Unimplemented: non-greedy quantifiers ───────────────────────────────────

    (r"a*?",      "aaa",    "fullmatch"),  # lazy *?: same language as a*
    (r"a*?",      "",       "fullmatch"),
    (r"a+?",      "a",      "fullmatch"),  # lazy +?: same language as a+
    (r"a+?",      "aaa",    "fullmatch"),
    (r"a??",      "",       "fullmatch"),  # lazy ??: same language as a?
    (r"a??",      "a",      "fullmatch"),
    (r"a*?b",     "aaab",   "search"),  # lazy in search mode
    (r"a+?b",     "ab",     "search"),

    # ── Unimplemented: \d \w \s shorthand classes ───────────────────────────────

    (r"\d",       "5",      "fullmatch"),
    (r"\d",       "a",      "fullmatch"),
    (r"\d+",      "123",    "fullmatch"),
    (r"\d+",      "12a",    "fullmatch"),  # partial: Python noMatch
    (r"\D",       "a",      "fullmatch"),
    (r"\D",       "5",      "fullmatch"),
    (r"\w",       "a",      "fullmatch"),
    (r"\w",       "!",      "fullmatch"),
    (r"\w+",      "hello",  "fullmatch"),
    (r"\W",       "!",      "fullmatch"),
    (r"\W",       "a",      "fullmatch"),
    (r"\s",       " ",      "fullmatch"),
    (r"\s",       "a",      "fullmatch"),
    (r"\S",       "a",      "fullmatch"),
    (r"\S",       " ",      "fullmatch"),
    (r"\d+\s\w+", "42 abc", "fullmatch"),  # combined shorthands

    # ── Unimplemented: \b \B word-boundary assertions ───────────────────────────

    (r"\bcat\b",      "cat",          "search"),  # exact word
    (r"\bcat\b",      "cats",         "search"),  # trailing char: no boundary after t
    (r"\bcat\b",      "the cat now",  "search"),  # word surrounded by spaces
    (r"\bcat\b",      "concatenate",  "search"),  # no boundary: cat inside word
    (r"\Bcat\B",      "concatenate",  "search"),  # \B: non-boundary on both sides

    # ── Unimplemented: \A \Z absolute anchors ───────────────────────────────────

    (r"\Aa",      "abc",    "search"),  # \A forces match at absolute start
    (r"\Aa",      "xabc",   "search"),  # prefix not allowed
    (r"a\Z",      "ba",     "search"),  # \Z forces match at absolute end
    (r"a\Z",      "ab",     "search"),  # suffix not allowed
    (r"\Aa\Z",    "a",      "fullmatch"),
    (r"\Aa\Z",    "ab",     "fullmatch"),

    # ── Unimplemented: non-capturing groups (?:...) ─────────────────────────────

    (r"(?:ab)+",    "abab",  "fullmatch"),  # same language as (ab)+
    (r"(?:ab)+",    "ab",    "fullmatch"),
    (r"(?:a|b)+",   "abba",  "fullmatch"),
    (r"x(?:a|b)y",  "xay",   "fullmatch"),
    (r"x(?:a|b)y",  "xcy",   "fullmatch"),

    # ── Unimplemented: named groups (?P<name>...) ───────────────────────────────

    (r"(?P<x>a)",           "a",   "fullmatch"),
    (r"(?P<x>a)",           "b",   "fullmatch"),
    (r"(?P<x>a)(?P<y>b)",   "ab",  "fullmatch"),

    # ── Unimplemented: inline flags (?i) (?m) (?s) ─────────────────────────────

    (r"(?i)hello",   "HELLO",  "fullmatch"),  # case-insensitive
    (r"(?i)hello",   "Hello",  "fullmatch"),
    (r"(?i)hello",   "world",  "fullmatch"),
    (r"(?i)[a-z]+",  "ABC",    "fullmatch"),
    (r"(?s)a.b",     "axb",    "fullmatch"),  # (?s): . matches anything (no \n in test)
    (r"(?m)^a",      "a",      "search"),  # (?m): ^ matches start of each line

    # ── Unimplemented: backreferences ───────────────────────────────────────────

    (r"(a)\1",    "aa",   "fullmatch"),  # group 1 repeated
    (r"(a)\1",    "ab",   "fullmatch"),
    (r"(a|b)\1",  "aa",   "fullmatch"),
    (r"(a|b)\1",  "bb",   "fullmatch"),
    (r"(a|b)\1",  "ab",   "fullmatch"),  # mismatch
    (r"(.)\1",    "aa",   "fullmatch"),  # any char repeated
    (r"(.)\1",    "ab",   "fullmatch"),
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

    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
