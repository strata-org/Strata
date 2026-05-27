def compute(x: int, y):
    return x + y

def test_mixed_typed_untyped():
    r = compute(3, 7)
    assert r == 10, "mixed typed and untyped params"

test_mixed_typed_untyped()
