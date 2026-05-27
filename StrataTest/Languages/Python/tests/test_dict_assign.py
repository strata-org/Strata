def test_dict_assign():
    d = {"x": 10}
    d["x"] = 20
    assert d["x"] == 20, "dict update"

test_dict_assign()
