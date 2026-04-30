def test_str_concat():
    a: str = "hello"
    b: str = " world"
    c: str = a + b
    assert c == "hello world", "string concat"

test_str_concat()
