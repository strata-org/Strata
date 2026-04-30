def outer(x: int) -> int:
    def inner(y: int) -> int:
        return y + 1
    return inner(x) + inner(x)

def test_nested_func():
    assert outer(5) == 12, "nested function"

test_nested_func()
