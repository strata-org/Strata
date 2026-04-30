def test_for_nested():
    outer = [1, 2, 3]
    inner = [10, 20]
    s: int = 0
    for a in outer:
        for b in inner:
            s = s + a * b
    assert s == 180, "nested for"

test_for_nested()
