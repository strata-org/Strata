def test_while_simple():
    i: int = 0
    s: int = 0
    while i < 5:
        s = s + i
        i = i + 1
    assert s == 10, "while sum"

test_while_simple()
