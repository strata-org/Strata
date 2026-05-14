class Val:
    n: int

    def __init__(self, n: int):
        self.n = n

def test_oop_object_equality():
    a = Val(5)
    b = Val(5)
    assert a.n == b.n, "same field values"

test_oop_object_equality()
