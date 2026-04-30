
class ClassA:
    def __init__(self, n: int):
        self.val : int = n

class ClassB:
    def __init__(self, n: int):
        self.val : int = n

def some_cond() -> bool :
    pass

class_a = ClassA(1)
class_b = ClassB(2)

a_val = class_a.val
b_val = class_b.val

cond = some_cond()

a_or_b : Any = class_a if cond else class_b

a_or_b.val = a_or_b.val * 2

assert (a_or_b.val == a_val * 2) or (a_or_b.val == b_val * 2)

assert cond or (class_a.val == a_val and class_b.val == b_val * 2)

assert (not cond) or (class_a.val == a_val * 2 and class_b.val == b_val)

assert class_a.val == a_val , "expected unknown"
