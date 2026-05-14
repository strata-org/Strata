def f(x: int) -> int:
    x = x + 10
    return x

def test_var_shadow_func():
    v: int = 5
    r: int = f(v)
    assert r == 15, "param modified inside"
    assert v == 5, "original unchanged"

test_var_shadow_func()
