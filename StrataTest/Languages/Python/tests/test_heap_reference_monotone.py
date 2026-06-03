class ClassA:
    def __init__(self, n: int):
        self.val : int = n

a1 = ClassA(1)
a2 = ClassA(2)

a1.val = 1
a2.val = 2

assert a1.val != a2.val
