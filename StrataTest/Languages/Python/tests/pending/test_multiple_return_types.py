def weird(x: int):
    if x > 0:
        return "positive"
    return 0

def test():
    r1 = weird(1)
    assert r1 == "positive", "returns str"
    r2 = weird(-1)
    assert r2 == 0, "returns int"
test()
