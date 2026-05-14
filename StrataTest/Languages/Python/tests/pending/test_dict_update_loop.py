def test_dict_update_loop():
    d = {}
    keys = ["a", "b", "c"]
    i: int = 0
    for k in keys:
        d[k] = i
        i = i + 1
    assert d["a"] == 0, "first"
    assert d["c"] == 2, "last"

test_dict_update_loop()
