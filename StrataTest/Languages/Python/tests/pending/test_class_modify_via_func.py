class Holder:
    n: int

    def __init__(self, n: int):
        self.n = n

def double_holder(h: Holder):
    h.n = h.n * 2

def test_class_modify_via_func():
    h = Holder(5)
    double_holder(h)
    assert h.n == 10, "modified via function"

test_class_modify_via_func()
