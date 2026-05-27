def test_if_elif_chain():
    x: int = 1
    r: int = 0
    if x == 1:
        r = 10
    elif x == 2:
        r = 20
    elif x == 3:
        r = 30
    else:
        r = 0
    assert r == 10, "elif chain"

test_if_elif_chain()
