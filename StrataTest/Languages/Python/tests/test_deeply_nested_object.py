class Inner:
    val: int
    def __init__(self, val: int):
        self.val = val

class Middle:
    inner: Inner
    def __init__(self, inner: Inner):
        self.inner = inner

class Outer:
    middle: Middle
    def __init__(self, middle: Middle):
        self.middle = middle

def test_oop_deeply_nested_field():
    """Three levels of nesting: Outer -> Middle -> Inner"""
    i = Inner(42)
    m = Middle(i)
    o = Outer(m)
    assert o.middle.inner.val == 42, "deeply nested field"

test_oop_deeply_nested_field()
