class MyClass:
    def __init__(self, ip1: int, ip2: str = "some str", ip3: int = 4, **args):
        pass

    def some_method(self, ip1: int, ip2: str = "some str", ip3: int = 4, **args)->int:
        return 1

c = MyClass (5, ip3 = 5, somekw = 9)
c.some_method (2, ip2 = "input 2", somekw=9)
