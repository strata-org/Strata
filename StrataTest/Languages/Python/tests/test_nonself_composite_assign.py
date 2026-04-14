class Inner:
    val: int

    def __init__(self, val: int):
        self.val = val

class Outer:
    inner: Inner

    def __init__(self, inner: Inner):
        self.inner = inner

def test_nonself_composite_assign():
    i = Inner(7)
    o = Outer(i)
    new_inner = Inner(99)
    o.inner = new_inner
    assert o.inner.val == 99, "non-self composite field reassignment"

test_nonself_composite_assign()
