def test_dict_overwrite():
    d = {"a": 1}
    d["a"] = 2
    d["a"] = 3
    assert d["a"] == 3, "dict overwrite"

test_dict_overwrite()
