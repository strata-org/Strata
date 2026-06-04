MyInt = int

def test():
    x: MyInt = 42
    assert x == 42, "type alias"
test()
