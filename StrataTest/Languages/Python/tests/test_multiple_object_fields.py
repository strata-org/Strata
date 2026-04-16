class Node:
    val: int
    def __init__(self, val: int):
        self.val = val

class Pair:
    left: Node
    right: Node
    def __init__(self, left: Node, right: Node):
        self.left = left
        self.right = right

def test_oop_multiple_object_fields():
    """Class with multiple fields of user-defined type"""
    a = Node(1)
    b = Node(2)
    p = Pair(a, b)
    assert p.left.val == 1, "left field"
    assert p.right.val == 2, "right field"

test_oop_multiple_object_fields()
