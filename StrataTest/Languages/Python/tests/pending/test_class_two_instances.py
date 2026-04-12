class Val:
    n: int

    def __init__(self, n: int):
        self.n = n

def test_class_two_instances():
    a = Val(1)
    b = Val(2)
    assert a.n == 1, "instance a"
    assert b.n == 2, "instance b"

test_class_two_instances()
