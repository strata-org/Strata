class Stack:
    items: int
    
    def __init__(self):
        self.items = 0

    def push(self):
        self.items = self.items + 1

    def push_two(self):
        self.push()
        self.push()

def test_oop_method_calls_method():
    s = Stack()
    s.push_two()
    assert s.items == 2, "method calls method"

test_oop_method_calls_method()
