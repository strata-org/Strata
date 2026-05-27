def test_int_parens():
    a: int = 2
    b: int = 3
    c: int = 4
    d: int = (a + b) * c
    assert d == 20, "parenthesized expression"

test_int_parens()
