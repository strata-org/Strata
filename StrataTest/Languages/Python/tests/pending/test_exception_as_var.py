def test():
    r: str = ""
    try:
        x: int = 1 // 0
    except ZeroDivisionError as e:
        r = "caught"
    assert r == "caught", "exception as var"
test()
