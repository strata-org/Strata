def test_list_concat():
    a = [1, 2]
    b = [3, 4]
    c = a + b
    assert c[0] == 1, "first"
    assert c[3] == 4, "last"

test_list_concat()
