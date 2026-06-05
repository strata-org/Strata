def noop():
    pass

def test():
    noop()
    assert True, "empty function"
test()
