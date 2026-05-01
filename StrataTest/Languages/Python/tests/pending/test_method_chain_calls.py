class Builder:
    parts: int

    def __init__(self):
        self.parts = 0

    def add_part(self):
        self.parts = self.parts + 1

def test_oop_method_chain_calls():
    b = Builder()
    b.add_part()
    b.add_part()
    b.add_part()
    b.add_part()
    assert b.parts == 4, "four parts added"

test_oop_method_chain_calls()
