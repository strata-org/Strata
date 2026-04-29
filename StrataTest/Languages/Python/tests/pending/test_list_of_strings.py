def test_list_of_strings():
    xs = ["a", "b", "c"]
    r: str = ""
    for s in xs:
        r = r + s
    assert r == "abc", "concat strings"

test_list_of_strings()
