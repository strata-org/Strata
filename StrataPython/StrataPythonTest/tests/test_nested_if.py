def test_nested_if():
    x: int = 5
    y: int = 10
    r: int = 0
    if x > 3:
        if y > 8:
            r = 1
    assert r == 1, "nested if"

test_nested_if()
