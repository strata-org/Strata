def add_one(x):
    return x + 1

def test_untyped_param():
    r = add_one(5)
    assert r == 6, "untyped param"

test_untyped_param()
