def test_nested_list():
    xs = [[1, 2], [3, 4]]
    assert xs[0][0] == 1, "nested access 0,0"
    assert xs[1][1] == 4, "nested access 1,1"

test_nested_list()
