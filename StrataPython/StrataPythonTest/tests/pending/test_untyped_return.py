def get_val():
    return 99

def test_untyped_return():
    r = get_val()
    assert r == 99, "untyped return"

test_untyped_return()
