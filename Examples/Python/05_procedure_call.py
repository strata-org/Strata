def add_one(x: int) -> int:
    return x + 1

def main():
    y: int = add_one(4)
    assert y == 5, "y should be 5"
