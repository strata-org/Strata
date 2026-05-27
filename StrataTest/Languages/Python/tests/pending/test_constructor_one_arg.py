class Wrapper:
    val: int

    def __init__(self, val: int):
        self.val = val

def test_oop_constructor_one_arg():
    w = Wrapper(42)
    assert w.val == 42, "field set by constructor"

test_oop_constructor_one_arg()
