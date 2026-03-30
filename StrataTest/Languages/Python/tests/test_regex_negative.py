import re

def main():
    # ── Expected failures ──
    # These assertions are intentionally wrong.  The solver should disprove
    # them, but currently returns 'unknown' instead of 'fail'.

    # Claim a non-match is a match
    m = re.fullmatch(r"a", "b")
    assert m != None, "EXPECTED_FAIL: fullmatch a on b"

    m = re.fullmatch(r"abc", "abd")
    assert m != None, "EXPECTED_FAIL: fullmatch abc on abd"

    m = re.fullmatch(r"[a-z]+", "ABC")
    assert m != None, "EXPECTED_FAIL: fullmatch [a-z]+ on ABC"

    # Anchors should prevent match
    m = re.fullmatch(r"^abc$", "abcd")
    assert m != None, "EXPECTED_FAIL: fullmatch ^abc$ on abcd"

    m = re.search(r"^abc", "xabc")
    assert m != None, "EXPECTED_FAIL: search ^abc in xabc"

    m = re.search(r"abc$", "abcx")
    assert m != None, "EXPECTED_FAIL: search abc$ in abcx"

    m = re.match(r"^a$", "ab")
    assert m != None, "EXPECTED_FAIL: match ^a$ in ab"

    # Compiled pattern with anchors
    p = re.compile(r"^abc$")
    m = re.search(p, "xabc")
    assert m != None, "EXPECTED_FAIL: compiled ^abc$ search xabc"

    m = re.match(p, "abcx")
    assert m != None, "EXPECTED_FAIL: compiled ^abc$ match abcx"

    # ── Malformed patterns (try/except) ────────────────────────────────
    # These currently return 'unknown'.

    caught = False
    try:
        m = re.fullmatch(r"(abc", "abc")
    except Exception:
        caught = True
    assert caught, "malformed: unmatched paren should raise"

    caught = False
    try:
        m = re.fullmatch(r"a**", "a")
    except Exception:
        caught = True
    assert caught, "malformed: nothing to repeat should raise"

    caught = False
    try:
        m = re.fullmatch(r"x{100,2}", "x")
    except Exception:
        caught = True
    assert caught, "malformed: bad bounds should raise"

    caught = False
    try:
        m = re.search(r"(abc", "xabcx")
    except Exception:
        caught = True
    assert caught, "malformed: search with bad pattern should raise"

    caught = False
    try:
        m = re.match(r"a**", "aaa")
    except Exception:
        caught = True
    assert caught, "malformed: match with bad pattern should raise"

    # ── Unsupported regex features ──────────────────────────────────────
    # Patterns using \S, \d, \w etc. are not yet supported by Strata's
    # regex compiler.  The result should be 'unknown' (sound over-approximation)
    # rather than an internal error.

    # Special sequences at top level
    m = re.search(r"^\S+$", "hello")
    assert m != None, "unsupported: search \\S+ should match non-empty non-whitespace"

    m = re.fullmatch(r"\d+", "123")
    assert m != None, "unsupported: fullmatch \\d+ on digit string"

    m = re.fullmatch(r"\w+", "hello_world")
    assert m != None, "unsupported: fullmatch \\w+ on word string"

    m = re.search(r"\s+", "hello world")
    assert m != None, "unsupported: search \\s+ finds whitespace"

    # Special sequences inside character classes
    m = re.fullmatch(r"[a-z\d]+", "abc123")
    assert m != None, "unsupported: fullmatch [a-z\\d]+ on alphanumeric"

    m = re.fullmatch(r"[\w\-]+", "hello-world")
    assert m != None, "unsupported: fullmatch [\\w\\-]+ on word with dash"

    # Escape sequences (string escapes, not regex metacharacter escapes)
    m = re.search(r"\t+", "\t\t")
    assert m != None, "unsupported: search \\t+ on tab string"

    m = re.fullmatch(r"[^\n]+", "hello")
    assert m != None, "unsupported: fullmatch [^\\n]+ on non-newline string"

    # Unsupported quantifiers and constructs
    m = re.search(r"ab.*?cd", "abXcd")
    assert m != None, "unsupported: non-greedy .*? quantifier"

    m = re.search(r"(?=foo)foo", "foobar")
    assert m != None, "unsupported: positive lookahead (?=foo)"

if __name__ == "__main__":
    main()
