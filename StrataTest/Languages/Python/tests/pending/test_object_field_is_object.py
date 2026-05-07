class Inner:
    val: int

    def __init__(self, val: int):
        self.val = val

class Outer:
    inner: Inner

    def __init__(self, inner: Inner):
        self.inner = inner

def test_oop_object_field_is_object():
    i = Inner(7)
    o = Outer(i)
    assert o.inner.val == 7, "nested object field"

test_oop_object_field_is_object()
