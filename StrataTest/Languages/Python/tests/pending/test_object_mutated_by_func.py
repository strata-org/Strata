class Holder:
    n: int

    def __init__(self, n: int):
        self.n = n

def double_it(h: Holder):
    h.n = h.n * 2

def test_oop_object_mutated_by_func():
    h = Holder(5)
    double_it(h)
    assert h.n == 10, "mutated by function"

test_oop_object_mutated_by_func()
