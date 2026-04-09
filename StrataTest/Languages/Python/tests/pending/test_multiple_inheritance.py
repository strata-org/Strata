class A:
    x: int
    def __init__(self):
        self.x = 1

class B:
    y: int
    def __init__(self):
        self.y = 2

class C(A, B):
    def __init__(self):
        self.x = 1
        self.y = 2

def test():
    c = C()
    assert c.x == 1, "from A"
    assert c.y == 2, "from B"
test()
