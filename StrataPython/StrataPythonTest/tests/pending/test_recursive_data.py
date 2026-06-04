class Node:
    val: int
    next_node: object

    def __init__(self, val: int):
        self.val = val
        self.next_node = None

def test():
    a = Node(1)
    b = Node(2)
    a.next_node = b
    assert a.next_node.val == 2, "linked list"
test()
