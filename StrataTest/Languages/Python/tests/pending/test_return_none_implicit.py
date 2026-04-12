def no_return():
    x: int = 1

def test_return_none_implicit():
    r = no_return()
    assert r is None, "implicit None return"

test_return_none_implicit()
