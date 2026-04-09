"""Regression test for evalIfCanonical on regex functions (Issue #812).

Tests that re.search/re.match/re.fullmatch work when the pattern is a
constant string but the string being matched is symbolic (a variable).
Without evalIfCanonical, the concreteEval would never fire and the
regex call would remain an opaque uninterpreted function, causing
verification to fail.
"""

import re

def test_search_symbolic(x: str):
    """re.search with symbolic argument."""
    if x == "beginning":
        m = re.search(r"^begin", x)
        assert m != None, "search should match: x starts with 'begin'"

def test_match_symbolic(x: str):
    """re.match with symbolic argument."""
    if x == "hello":
        m = re.match(r"hel", x)
        assert m != None, "match should match: x starts with 'hel'"

def test_fullmatch_symbolic(x: str):
    """re.fullmatch with symbolic argument."""
    if x == "abc":
        m = re.fullmatch(r"[a-z]+", x)
        assert m != None, "fullmatch should match: x is all lowercase"
