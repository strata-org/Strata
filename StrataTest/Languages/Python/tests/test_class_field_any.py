class MyClass:
    def __init__(self, some_field):
        self.some_field: Any = some_field

c = MyClass([1,2])
assert c.some_field == [1,2]
