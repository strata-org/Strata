class Shared:
    count: int = 0

def test():
    a = Shared()
    b = Shared()
    Shared.count = 10
    assert Shared.count == 10, "class variable"
test()
