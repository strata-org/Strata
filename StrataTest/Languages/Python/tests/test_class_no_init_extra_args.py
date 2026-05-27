class NoInit:
    x: int = 5

def test():
    n = NoInit(42)
test()
