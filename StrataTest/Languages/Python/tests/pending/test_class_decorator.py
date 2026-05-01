def add_method(cls):
    cls.extra = 42
    return cls

@add_method
class MyClass:
    pass

def test():
    assert MyClass.extra == 42, "class decorator"
test()
