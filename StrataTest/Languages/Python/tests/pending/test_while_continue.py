def test_while_continue():
    i: int = 0
    s: int = 0
    while i < 10:
        i = i + 1
        if i % 2 == 0:
            continue
        s = s + 1
    assert s == 5, "while continue counts odds"

test_while_continue()
