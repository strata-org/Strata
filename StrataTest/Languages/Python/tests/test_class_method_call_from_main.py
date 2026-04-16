# Test that class method calls from __main__ are properly lowered
# (not replaced with holes). The assert inside greet() should be
# reachable and verified.

class Greeter:
    def __init__(self, name: str):
        self.name: str = name

    def greet(self) -> str:
        assert self.name != "", "name must not be empty"
        return self.name

if __name__ == "__main__":
    g: Greeter = Greeter("hello")
    msg: str = g.greet()
