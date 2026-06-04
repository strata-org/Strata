class NoInit:
    x: int = 5

def test():
    n = NoInit()
    assert n.x == 5, "class without __init__"
test()
