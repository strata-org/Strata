# Resolved: analyzer can now resolve bool(x) == y equality assertions
# See https://github.com/strata-org/Strata/issues/945

def test_bool_none():
    assert bool(None) == False

def test_bool_bool():
    assert bool(True) == True
    assert bool(False) == False

def test_bool_int():
    assert bool(0) == False
    assert bool(1) == True
    assert bool(-1) == True

def test_bool_str():
    assert bool("") == False
    assert bool("x") == True

def test_bool_list():
    assert bool([]) == False
    assert bool([1]) == True

def test_bool_dict():
    assert bool({}) == False
    assert bool({"a": 1}) == True

def test_bool_float():
    assert bool(0.0) == False
    assert bool(1.5) == True
    assert bool(-0.0) == False

test_bool_none()
test_bool_bool()
test_bool_int()
test_bool_float()
test_bool_str()
test_bool_list()
test_bool_dict()
