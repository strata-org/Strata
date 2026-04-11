def divmod_manual(a: int, b: int):
    return a // b, a % b

def test_tuple_return():
    q, r = divmod_manual(17, 5)
    assert q == 3, "quotient"
    assert r == 2, "remainder"

test_tuple_return()
