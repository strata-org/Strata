class Base:
    val: int
    def __init__(self, val: int):
        self.val = val

class Child(Base):
    extra: int
    def __init__(self, val: int, extra: int):
        super().__init__(val)
        self.extra = extra

def test():
    c = Child(10, 20)
    assert c.val == 10, "super init"
    assert c.extra == 20, "child field"
test()
