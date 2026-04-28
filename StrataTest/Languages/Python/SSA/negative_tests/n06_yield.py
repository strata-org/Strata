# Negative test: yield/generator function → stub
# Expected: warning about unsupported yield, stub generated

def count_up(n: int):
    i = 0
    while i < n:
        yield i
        i += 1

def normal_func(x: int) -> int:
    return x * 2
