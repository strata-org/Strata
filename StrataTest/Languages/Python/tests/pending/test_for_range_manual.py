def test():
    s: int = 0
    items = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    for i in items:
        s = s + i
    assert s == 45, "sum 0..9"
test()
