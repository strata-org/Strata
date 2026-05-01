from typing import Any

class Greeter:
    msg: str

    def __init__(self, msg: str):
        self.msg = msg

    def greet(self) -> str:
        return self.msg

def test_any_method_call():
    g: Any = Greeter("hi")
    r = g.greet()
    assert r == "hi", "method call on Any"

test_any_method_call()
