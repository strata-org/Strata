def my_decorator(func):
    def wrapper():
        return func() + 1
    return wrapper

@my_decorator
def get_five():
    return 5

def test():
    assert get_five() == 6, "decorator"
test()
