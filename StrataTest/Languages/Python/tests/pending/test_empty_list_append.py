def test():
    xs = []
    i: int = 0
    while i < 100:
        xs.append(i)
        i = i + 1
    assert xs[99] == 99, "100 appends"
test()
