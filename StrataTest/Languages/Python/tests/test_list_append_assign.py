def test():
    xs = [1, 2, 3]
    y = xs.append(4)
    assert xs == [1, 2, 3, 4]
    assert y == None  
