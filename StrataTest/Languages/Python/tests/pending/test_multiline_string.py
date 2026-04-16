def test():
    s: str = """line1
line2
line3"""
    assert "line2" in s, "multiline string"
test()
