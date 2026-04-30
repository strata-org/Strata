class Val:
    n: int

    def __init__(self, n: int):
        self.n = n

def test_oop_two_objects_independent():
    a = Val(1)
    b = Val(2)
    a.n = 10
    assert a.n == 10, "a modified"
    assert b.n == 2, "b independent"

test_oop_two_objects_independent()
