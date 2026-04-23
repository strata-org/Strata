counter: int = 0

def step() -> None:
    global counter
    counter = counter + 1

def double_step() -> None:
    step()
    step()

def main() -> None:
    double_step()
    assert counter == 2
