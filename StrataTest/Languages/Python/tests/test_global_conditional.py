flag: int = 0

def maybe_set(cond: bool) -> None:
    global flag
    if cond:
        flag = 1
    else:
        flag = 0

def main() -> None:
    maybe_set(True)
    assert flag == 1
    maybe_set(False)
    assert flag == 0
