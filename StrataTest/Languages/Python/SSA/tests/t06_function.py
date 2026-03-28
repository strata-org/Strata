# Test: FunctionDef, Return, Call, keyword args

def add(a: int, b: int) -> int:
    return a + b

def greet(name: str, greeting: str = "Hello") -> str:
    return greeting + " " + name

result = add(1, 2)
msg = greet("world")
msg2 = greet("world", greeting="Hi")

# Void function (no return value)
def do_nothing():
    pass

do_nothing()
