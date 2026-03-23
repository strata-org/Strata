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

    # Group loops
    m = re.fullmatch(r"(ab){2}", "abab")
    assert m != None, "fullmatch group loop match"

    m = re.fullmatch(r"(ab){2}", "ab")
    assert m == None, "fullmatch group loop too few"

    m = re.fullmatch(r"(ab){2,3}", "ababab")
    assert m != None, "fullmatch group loop 3 reps"

    m = re.fullmatch(r"(ab){2,3}", "ab")
    assert m == None, "fullmatch group loop 1 rep"

    # ── Anchors: basic behavior ──────────────────────────────────────

    # fullmatch: ^ and $ are redundant (whole string must match)
    m = re.fullmatch(r"^a", "a")
    assert m != None, "fullmatch ^a match"

    m = re.fullmatch(r"^a", "ba")
    assert m == None, "fullmatch ^a reject"

    m = re.fullmatch(r"a$", "a")
    assert m != None, "fullmatch a$ match"

    m = re.fullmatch(r"a$", "ab")
    assert m == None, "fullmatch a$ reject"

    m = re.fullmatch(r"^a$", "a")
    assert m != None, "fullmatch ^a$ match"

    m = re.fullmatch(r"^a$", "ab")
    assert m == None, "fullmatch ^a$ reject trailing"

    m = re.fullmatch(r"^a$", "ba")
    assert m == None, "fullmatch ^a$ reject leading"

    # ^$ matches only the empty string
    m = re.fullmatch(r"^$", "")
    assert m != None, "fullmatch ^$ on empty"

    m = re.fullmatch(r"^$", "a")
    assert m == None, "fullmatch ^$ on non-empty"

    m = re.match(r"^$", "")
    assert m != None, "match ^$ on empty"

    m = re.match(r"^$", "a")
    assert m == None, "match ^$ on non-empty"

    m = re.search(r"^$", "")
    assert m != None, "search ^$ on empty"

    m = re.search(r"^$", "a")
    assert m == None, "search ^$ on non-empty"

    # ── Anchors in match mode ────────────────────────────────────────

    # ^ is a no-op in match (already anchored at start)
    m = re.match(r"^a", "a")
    assert m != None, "match ^a"

    m = re.match(r"^a", "ab")
    assert m != None, "match ^a trailing ok"

    m = re.match(r"^a", "ba")
    assert m == None, "match ^a reject"

    # $ cuts off trailing content
    m = re.match(r"^a$", "a")
    assert m != None, "match ^a$ exact"

    m = re.match(r"^a$", "ab")
    assert m == None, "match ^a$ reject trailing"

    m = re.match(r"a$", "a")
    assert m != None, "match a$ exact"

    m = re.match(r"a$", "ab")
    assert m == None, "match a$ reject trailing"

    m = re.match(r"a.*$", "axyz")
    assert m != None, "match a.*$ accepts"

    m = re.match(r"a.*$", "b")
    assert m == None, "match a.*$ rejects"

    # ── Anchors in search mode ───────────────────────────────────────

    # basic search
    m = re.search(r"a", "xax")
    assert m != None, "search a in middle"

    m = re.search(r"a", "xyz")
    assert m == None, "search a not found"

    # ^ prevents free prefix
    m = re.search(r"^a", "abc")
    assert m != None, "search ^a at start"

    m = re.search(r"^a", "xabc")
    assert m == None, "search ^a reject non-start"

    m = re.search(r"^a", "a")
    assert m != None, "search ^a exact"

    # $ prevents free suffix
    m = re.search(r"a$", "ba")
    assert m != None, "search a$ at end"

    m = re.search(r"a$", "ab")
    assert m == None, "search a$ reject non-end"

    m = re.search(r"a$", "xyzba")
    assert m != None, "search a$ deep end"

    m = re.search(r"a$", "xyzbax")
    assert m == None, "search a$ reject trailing"

    # ^...$ in search: forces exact match
    m = re.search(r"^a$", "a")
    assert m != None, "search ^a$ exact"

    m = re.search(r"^a$", "xa")
    assert m == None, "search ^a$ reject prefix"

    m = re.search(r"^a$", "ax")
    assert m == None, "search ^a$ reject suffix"

    # ── Multi-char anchors in search ─────────────────────────────────

    m = re.search(r"^abc", "abcxyz")
    assert m != None, "search ^abc at start"

    m = re.search(r"^abc", "xabc")
    assert m == None, "search ^abc reject non-start"

    m = re.search(r"abc$", "xyzabc")
    assert m != None, "search abc$ at end"

    m = re.search(r"abc$", "abcx")
    assert m == None, "search abc$ reject non-end"

    m = re.search(r"^abc$", "abc")
    assert m != None, "search ^abc$ exact"

    m = re.search(r"^abc$", "xabc")
    assert m == None, "search ^abc$ reject prefix"

    m = re.search(r"^abc$", "abcx")
    assert m == None, "search ^abc$ reject suffix"

    # ── Anchors with quantifiers ─────────────────────────────────────

    m = re.fullmatch(r"^a{3}$", "aaa")
    assert m != None, "fullmatch ^a{3}$ match"

    m = re.fullmatch(r"^a{3}$", "aa")
    assert m == None, "fullmatch ^a{3}$ too few"

    m = re.fullmatch(r"^a{3}$", "aaaa")
    assert m == None, "fullmatch ^a{3}$ too many"

    m = re.match(r"^a{3}$", "aaa")
    assert m != None, "match ^a{3}$ exact"

    m = re.match(r"^a{3}$", "aaab")
    assert m == None, "match ^a{3}$ reject trailing"

    m = re.match(r"a{3}", "aaab")
    assert m != None, "match a{3} trailing ok"

    # ── Escaped metacharacters ───────────────────────────────────────

    m = re.fullmatch(r"a\.b", "a.b")
    assert m != None, "escaped dot matches literal"

    m = re.fullmatch(r"a\.b", "axb")
    assert m == None, "escaped dot rejects non-dot"

    m = re.fullmatch(r"a\+b", "a+b")
    assert m != None, "escaped plus matches literal"

    m = re.fullmatch(r"a\+b", "ab")
    assert m == None, "escaped plus rejects"

    m = re.fullmatch(r"a\*b", "a*b")
    assert m != None, "escaped star matches literal"

    m = re.fullmatch(r"a\*b", "aab")
    assert m == None, "escaped star rejects"

    m = re.fullmatch(r"a\?b", "a?b")
    assert m != None, "escaped question matches literal"

    m = re.fullmatch(r"a\?b", "ab")
    assert m == None, "escaped question rejects"

    m = re.fullmatch(r"a\(b\)", "a(b)")
    assert m != None, "escaped parens match literal"

    m = re.fullmatch(r"a\(b\)", "ab")
    assert m == None, "escaped parens reject"

    m = re.fullmatch(r"a\\b", "a\\b")
    assert m != None, "escaped backslash matches literal"

    m = re.fullmatch(r"a\\b", "ab")
    assert m == None, "escaped backslash rejects"

    # Escaped metacharacters with search
    m = re.search(r"a\.b", "xa.by")
    assert m != None, "search escaped dot"

    m = re.search(r"a\\b", "xa\\by")
    assert m != None, "search escaped backslash"

    m = re.search(r"a\\b", "xaby")
    assert m == None, "search escaped backslash reject"

    # ── Colon in patterns ────────────────────────────────────────────

    m = re.fullmatch(r"a:b", "a:b")
    assert m != None, "colon literal match"

    m = re.fullmatch(r"a:b", "ab")
    assert m == None, "colon literal reject"

    m = re.fullmatch(r"[a-z]+:[0-9]+", "foo:42")
    assert m != None, "colon class match"

    m = re.fullmatch(r"[a-z]+:[0-9]+", "foo42")
    assert m == None, "colon class reject"

    m = re.search(r"[a-z]+:[0-9]+", "xfoo:42y")
    assert m != None, "search colon class"

    m = re.match(r"^[a-z]+:[0-9]+$", "foo:42")
    assert m != None, "match anchored colon"

    m = re.match(r"^[a-z]+:[0-9]+$", "foo:42x")
    assert m == None, "match anchored colon reject trailing"

    # ── Multi-char patterns ──────────────────────────────────────────

    m = re.fullmatch(r"abc.*def", "abcdef")
    assert m != None, "wildcard empty middle"

    m = re.fullmatch(r"abc.*def", "abcXXdef")
    assert m != None, "wildcard non-empty middle"

    m = re.fullmatch(r"abc.*def", "abcXXdeg")
    assert m == None, "wildcard wrong ending"

    m = re.search(r"abc.*def", "xabcXXdefy")
    assert m != None, "search wildcard"

    # Multi-char alternation
    m = re.fullmatch(r"abc|def", "abc")
    assert m != None, "multi-char alt first"

    m = re.fullmatch(r"abc|def", "def")
    assert m != None, "multi-char alt second"

    m = re.fullmatch(r"abc|def", "abcdef")
    assert m == None, "multi-char alt reject concat"

    m = re.search(r"abc|def", "xdefy")
    assert m != None, "search multi-char alt"

    # ── Anchors inside alternation ───────────────────────────────────

    m = re.fullmatch(r"^a|b$", "a")
    assert m != None, "fullmatch ^a|b$ first branch"

    m = re.fullmatch(r"^a|b$", "b")
    assert m != None, "fullmatch ^a|b$ second branch"

    m = re.fullmatch(r"^a|b$", "ab")
    assert m == None, "fullmatch ^a|b$ reject"

    m = re.search(r"^a|b$", "axyz")
    assert m != None, "search ^a|b$ start anchor"

    m = re.search(r"^a|b$", "xyzb")
    assert m != None, "search ^a|b$ end anchor"

    m = re.search(r"^a|b$", "xyzc")
    assert m == None, "search ^a|b$ neither"

    # ── Compile + anchors: mode applied at match time ────────────────

    p = re.compile(r"^abc$")

    m = re.fullmatch(p, "abc")
    assert m != None, "compiled ^abc$ fullmatch"

    m = re.search(p, "abc")
    assert m != None, "compiled ^abc$ search exact"

    m = re.search(p, "xabc")
    assert m == None, "compiled ^abc$ search reject prefix"

    m = re.match(p, "abc")
    assert m != None, "compiled ^abc$ match exact"

    m = re.match(p, "abcx")
    assert m == None, "compiled ^abc$ match reject trailing"

    # ── Malformed patterns (pattern errors) ──────────────────────────
    # Our pipeline returns exception(RePatternError(...)) for genuinely
    # malformed patterns, modeling Python's re.error.
    # The solver proves exception(...) != from_none(), so these pass.

    m = re.fullmatch(r"(abc", "abc")
    assert m != None, "malformed: unmatched paren is exception, not None"

    m = re.fullmatch(r"a**", "a")
    assert m != None, "malformed: nothing to repeat is exception, not None"

    m = re.fullmatch(r"x{100,2}", "x")
    assert m != None, "malformed: bad bounds is exception, not None"

    m = re.search(r"(abc", "xabcx")
    assert m != None, "malformed: search with bad pattern is exception, not None"

    m = re.match(r"a**", "aaa")
    assert m != None, "malformed: match with bad pattern is exception, not None"

if __name__ == "__main__":
    main()
