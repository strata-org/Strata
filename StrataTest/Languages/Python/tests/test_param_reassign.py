def single_param_reassign(x: int) -> int:
    x = x + 1
    return x

def multi_param_reassign(a: int, b: int) -> int:
    a = a + 1
    b = b * 2
    return a + b

def no_param_reassign(x: int, y: int) -> int:
    return x + y

def partial_param_reassign(x: int, y: int) -> int:
    x = x + y
    return x

def param_reassign_twice(x: int) -> int:
    x = x + 1
    x = x * 2
    return x

def test_param_reassign():
    r1: int = single_param_reassign(5)
    assert r1 == 6, "single reassign"

    r2: int = multi_param_reassign(3, 4)
    assert r2 == 12, "multi reassign"

    r3: int = no_param_reassign(2, 3)
    assert r3 == 5, "no reassign"

    r4: int = partial_param_reassign(10, 5)
    assert r4 == 15, "partial reassign"

    r5: int = param_reassign_twice(3)
    assert r5 == 8, "reassign twice"

test_param_reassign()
