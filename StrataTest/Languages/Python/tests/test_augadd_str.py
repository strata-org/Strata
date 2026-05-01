def test_augadd_str():
    s: str = "hello"
    s += " world"
    assert s == "hello world", "augmented add string"

test_augadd_str()
