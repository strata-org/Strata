class Doubler:
    def __init__(self):
        pass

    def double(self, x):
        return x * 2

def test_untyped_class_method():
    d = Doubler()
    r = d.double(5)
    assert r == 10, "untyped method"

test_untyped_class_method()
