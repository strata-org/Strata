# Pending: analyzer cannot resolve bool(x) == y for float arguments
# See https://github.com/strata-org/Strata/issues/945

def test_bool_float():
    assert bool(0.0) == False
    assert bool(1.5) == True
    assert bool(-0.0) == False

test_bool_float()
