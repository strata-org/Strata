def test():
    x: int = 2
    r: int = 0
    match x:
        case 1:
            r = 10
        case 2:
            r = 20
        case _:
            r = 0
    assert r == 20, "match statement"
test()
