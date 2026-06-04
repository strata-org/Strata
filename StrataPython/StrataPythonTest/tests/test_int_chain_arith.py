def test_int_chain_arith():
    a: int = 2
    b: int = 3
    c: int = 4
    d: int = a + b * c
    assert d == 14, "operator precedence"

test_int_chain_arith()
