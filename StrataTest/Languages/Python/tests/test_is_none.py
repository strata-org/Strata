def test_is_none():
    x: int = 2
    y : int = 0
    if x is None:
        y = 1
    assert y == 0, "x is not None"
    return

def test_is_not_none():
    y: int = 3
    x : int = 1
    if y is not None:
        x = 2
    assert x==2,"y is not None"
    return

def test_is_none_variable():
    z = None
    assert z is None, "z should be None"

def test_is_not_none_variable():
    w: int = 5
    assert w is not None, "w should not be None"

def test_int_is_not_none_negative():
    x: int = 5
    assert not (x is None), "int is not None"

def test_none_is_not_not_none_negative():
    z = None
    assert not (z is not None), "None is not 'not None'"
