def identity(x: int) -> int:
    return x

def test_int_identity():
    assert identity(42) == 42, "identity function"

test_int_identity()
