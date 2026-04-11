counter: int = 0

def inc():
    global counter
    counter = counter + 1

def test():
    inc()
    inc()
    assert counter == 2, "global keyword"
test()
