# Pending: analyzer cannot resolve not/and/or with float operands
# See https://github.com/strata-org/Strata/issues/947

def test_and_float():
    assert (0.0 and "x") == 0.0
    assert (1.5 and "x") == "x"

def test_or_float():
    assert (0.0 or "x") == "x"
    assert (1.5 or "x") == 1.5

def test_not_float():
    assert (not 0.0) == True
    assert (not 1.5) == False

test_and_float()
test_or_float()
test_not_float()
