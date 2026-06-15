class MultiField:
    x: int = 1
    y: int = 2
    z: str = "hello"

def test():
    m = MultiField()
    assert True, "class with multiple annotated fields no init"
test()
