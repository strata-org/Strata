total: int = 0

def add_to_total(n: int) -> None:
    global total
    total = total + n

def main() -> None:
    add_to_total(5)
    add_to_total(3)
    assert total == 8
