class Dog:
    name: str

    def __init__(self, name: str):
        self.name = name

class Cat:
    name: str

    def __init__(self, name: str):
        self.name = name

def test_oop_multiple_classes():
    d = Dog("Rex")
    c = Cat("Whiskers")
    assert d.name == "Rex", "dog name"
    assert c.name == "Whiskers", "cat name"

test_oop_multiple_classes()
