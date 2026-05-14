def test_list_falsy():
    xs = []
    r: int = 0
    if xs:
        r = 1
    assert r == 0, "empty list is falsy"

test_list_falsy()
