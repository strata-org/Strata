def test_var_reassign():
    x: int = 1
    x = 2
    x = 3
    assert x == 3, "reassignment"

test_var_reassign()
