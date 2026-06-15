def test_list_truthy():
    xs = [1]
    r: int = 0
    if xs:
        r = 1
    assert r == 1, "nonempty list is truthy"

test_list_truthy()
