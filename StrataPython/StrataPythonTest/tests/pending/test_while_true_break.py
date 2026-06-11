def test():
    i: int = 0
    while True:
        i = i + 1
        if i == 5:
            break
    assert i == 5, "while True with break"
test()
