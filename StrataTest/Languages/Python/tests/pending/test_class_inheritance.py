class Animal:
    name: str

    def __init__(self, name: str):
        self.name = name

class Dog(Animal):
    breed: str

    def __init__(self, name: str, breed: str):
        self.name = name
        self.breed = breed

def test():
    d = Dog("Rex", "Lab")
    assert d.name == "Rex", "inherited field"
    assert d.breed == "Lab", "own field"
test()
