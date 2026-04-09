def test_dict_iter_keys():
    d = {"a": 1, "b": 2, "c": 3}
    count: int = 0
    for k in d:
        count = count + 1
    assert count == 3, "dict key iteration"

test_dict_iter_keys()
