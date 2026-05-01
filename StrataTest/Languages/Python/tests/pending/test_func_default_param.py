def greet(n: int = 5) -> int:
    return n + 1

def test_func_default_param():
    assert greet() == 6, "default param"
    assert greet(10) == 11, "override default"

test_func_default_param()
