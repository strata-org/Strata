class Wrapper:
    val: int

    def __init__(self, val: int):
        self.val = val

def extract(w: Wrapper) -> int:
    return w.val

def test_class_pass_as_arg():
    w = Wrapper(42)
    assert extract(w) == 42, "pass object as arg"

test_class_pass_as_arg()
