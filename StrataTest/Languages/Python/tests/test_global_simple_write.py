counter: int = 0

def increment() -> None:
    global counter
    counter = counter + 1

def main() -> None:
    increment()
    assert counter == 1
