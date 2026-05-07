def test_str_in():
    s: str = "hello world"
    assert "world" in s, "substring in"
    assert "xyz" not in s, "substring not in"

test_str_in()
