# strata-args: --check-mode bugFinding --check-level full
class ClassA:
    def __init__(self, n: int):
        self.val : int = n

class ClassB:
    def __init__(self, n: int):
        self.val : int = n

def pure_double(buf: Any) -> int :
    return buf.val * 2

def modified_double(buf: Any):
    buf.val *= 2

class_a = ClassA(1)
r1 = pure_double(class_a)
assert r1 == 2

class_b = ClassB(2)
r2 = pure_double(class_b)
assert r2 == 4

modified_double(class_a)
assert class_a.val == 2
