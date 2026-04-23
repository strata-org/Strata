x: int = 0
y: int = 0

def set_both() -> None:
    global x, y
    x = 10
    y = 20

def main() -> None:
    set_both()
    assert x == 10
    assert y == 20
