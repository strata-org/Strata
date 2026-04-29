def test():
    x: int = 5
    if x > 10:
        assert False, "unreachable"
    assert True, "reachable"
test()
