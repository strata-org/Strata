def test():
    x: int = 5
    del x
    try:
        y = x
        assert False, "should have raised"
    except NameError:
        assert True, "del worked"
test()
