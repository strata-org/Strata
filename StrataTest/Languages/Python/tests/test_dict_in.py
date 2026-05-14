def test_dict_in():
    d = {"a": 1, "b": 2}
    assert "a" in d, "key in dict"
    assert "c" not in d, "key not in dict"

test_dict_in()
