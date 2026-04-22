# Pending: analyzer cannot resolve and/or with float operands
# See https://github.com/strata-org/Strata/issues/947

def test_and_float():
    assert (0.0 and "x") == 0.0
    assert (1.5 and "x") == "x"

def test_or_float():
    assert (0.0 or "x") == "x"
    assert (1.5 or "x") == 1.5

test_and_float()
test_or_float()
