a: int = 0
b: int = 0

def write_a() -> None:
    global a
    a = 1

def write_b() -> None:
    global b
    b = 2

def main() -> None:
    write_a()
    write_b()
    assert a == 1
    assert b == 2
