def f() -> int:
    x: int = 10
    return x

def test_func_local_scope():
    x: int = 99
    r: int = f()
    assert r == 10, "local scope"
    assert x == 99, "outer unchanged"

test_func_local_scope()
