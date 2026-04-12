class Empty:
    pass

def test():
    e = Empty()
    assert e is not None, "empty class"
test()
