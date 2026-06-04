def noop():
    return

def test():
    r = noop()
    assert r is None, "return nothing"
test()
