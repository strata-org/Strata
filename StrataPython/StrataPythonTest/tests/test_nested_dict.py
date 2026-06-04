def test():
    d = {"a": {"b": {"c": 42}}}
    assert d["a"]["b"]["c"] == 42, "nested dict"
test()
