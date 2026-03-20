import re

def main():
    # ── re.fullmatch: entire string must match ──────────────────────────

    # Literal match
    m = re.fullmatch(r"abc", "abc")
    assert m != None, "fullmatch literal should match"

    m = re.fullmatch(r"abc", "abcd")
    assert m == None, "fullmatch literal should reject extra chars"

    # Character class
    m = re.fullmatch(r"[a-z]+", "hello")
    assert m != None, "fullmatch char class should match"

    m = re.fullmatch(r"[a-z]+", "Hello")
    assert m == None, "fullmatch char class should reject uppercase"

    # Negated class
    m = re.fullmatch(r"[^0-9]+", "hello")
    assert m != None, "fullmatch negated class should match non-digits"

    m = re.fullmatch(r"[^0-9]+", "hello123")
    assert m == None, "fullmatch negated class should reject digits"

    # Dot (any char)
    m = re.fullmatch(r".+", "anything")
    assert m != None, "fullmatch dot-plus should match non-empty"

    m = re.fullmatch(r".", "ab")
    assert m == None, "fullmatch single dot should reject two chars"

    # Quantifiers: star
    m = re.fullmatch(r"a*", "")
    assert m != None, "fullmatch a* should match empty"

    m = re.fullmatch(r"a*", "aaa")
    assert m != None, "fullmatch a* should match repeated"

    m = re.fullmatch(r"a*", "b")
    assert m == None, "fullmatch a* should reject non-a"

    # Quantifiers: plus
    m = re.fullmatch(r"a+", "")
    assert m == None, "fullmatch a+ should reject empty"

    m = re.fullmatch(r"a+", "aaa")
    assert m != None, "fullmatch a+ should match one-or-more"

    # Quantifiers: optional
    m = re.fullmatch(r"ab?c", "ac")
    assert m != None, "fullmatch ab?c should match without b"

    m = re.fullmatch(r"ab?c", "abc")
    assert m != None, "fullmatch ab?c should match with b"

    m = re.fullmatch(r"ab?c", "abbc")
    assert m == None, "fullmatch ab?c should reject two b's"

    # Alternation
    m = re.fullmatch(r"cat|dog", "cat")
    assert m != None, "fullmatch alternation should match first"

    m = re.fullmatch(r"cat|dog", "dog")
    assert m != None, "fullmatch alternation should match second"

    m = re.fullmatch(r"cat|dog", "bird")
    assert m == None, "fullmatch alternation should reject other"

    # Concatenation
    m = re.fullmatch(r"[a-z]+[0-9]+", "abc123")
    assert m != None, "fullmatch concat should match"

    m = re.fullmatch(r"[a-z]+[0-9]+", "123abc")
    assert m == None, "fullmatch concat should reject wrong order"

    # ── re.match: anchored at start ─────────────────────────────────────

    m = re.match(r"[0-9]+", "123abc")
    assert m != None, "match should match at start"

    m = re.match(r"[0-9]+", "abc123")
    assert m == None, "match should reject when not at start"

    m = re.match(r"hello", "hello world")
    assert m != None, "match should match prefix"

    m = re.match(r"world", "hello world")
    assert m == None, "match should reject non-prefix"

    # ── re.search: match anywhere ───────────────────────────────────────

    m = re.search(r"[0-9]+", "abc123def")
    assert m != None, "search should find digits in middle"

    m = re.search(r"[0-9]+", "abcdef")
    assert m == None, "search should reject when no digits"

    m = re.search(r"xyz", "abcxyzdef")
    assert m != None, "search should find substring"

    m = re.search(r"xyz", "abcdef")
    assert m == None, "search should reject missing substring"

    # ── re.compile then match/search/fullmatch ──────────────────────────

    p = re.compile(r"[a-z]+")

    m = re.fullmatch(p, "hello")
    assert m != None, "compiled fullmatch should match"

    m = re.fullmatch(p, "Hello")
    assert m == None, "compiled fullmatch should reject uppercase"

    m = re.match(p, "hello123")
    assert m != None, "compiled match should match prefix"

    m = re.search(p, "123hello456")
    assert m != None, "compiled search should find in middle"

    # ── Edge cases ──────────────────────────────────────────────────────

    # Empty pattern
    m = re.fullmatch(r"", "")
    assert m != None, "fullmatch empty pattern on empty string"

    m = re.fullmatch(r"", "a")
    assert m == None, "fullmatch empty pattern on non-empty string"

    # Single char
    m = re.fullmatch(r"a", "a")
    assert m != None, "fullmatch single char"

    m = re.fullmatch(r"a", "b")
    assert m == None, "fullmatch single char mismatch"

    # Nested quantifiers
    m = re.fullmatch(r"(ab)+", "ababab")
    assert m != None, "fullmatch nested group-plus"

    m = re.fullmatch(r"(ab)+", "abba")
    assert m == None, "fullmatch nested group-plus mismatch"

    # Range with loop
    m = re.fullmatch(r"a{2,4}", "aa")
    assert m != None, "fullmatch loop min"

    m = re.fullmatch(r"a{2,4}", "aaaa")
    assert m != None, "fullmatch loop max"

    m = re.fullmatch(r"a{2,4}", "a")
    assert m == None, "fullmatch loop below min"

    m = re.fullmatch(r"a{2,4}", "aaaaa")
    assert m == None, "fullmatch loop above max"

if __name__ == "__main__":
    main()
