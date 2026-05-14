class Group:
    members: list

    def __init__(self):
        self.members = []

    def add(self, name: str):
        self.members.append(name)

def test_oop_class_with_list_field():
    g = Group()
    g.add("Alice")
    g.add("Bob")
    assert g.members[0] == "Alice", "first member"
    assert g.members[1] == "Bob", "second member"

test_oop_class_with_list_field()
