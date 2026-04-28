# Pending: analyzer cannot resolve (not x) == y equality assertions
# for int, float, str, list, dict
# See https://github.com/strata-org/Strata/issues/946

def test_not_int():
    assert (not 0) == True
    assert (not 1) == False

def test_not_float():
    assert (not 0.0) == True
    assert (not 3.14) == False

def test_not_str():
    assert (not "") == True
    assert (not "hi") == False

def test_not_list():
    assert (not []) == True
    assert (not [1]) == False

def test_not_dict():
    assert (not {}) == True
    assert (not {"k": "v"}) == False

test_not_int()
test_not_float()
test_not_str()
test_not_list()
test_not_dict()
