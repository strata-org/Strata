def test():
    x: int = 5
    r: int = 0
    if x > 0:
        if x > 1:
            if x > 2:
                if x > 3:
                    if x > 4:
                        r = 1
    assert r == 1, "deeply nested if"
test()
