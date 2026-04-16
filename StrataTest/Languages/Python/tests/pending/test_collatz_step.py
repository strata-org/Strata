def collatz_step(n: int) -> int:
    if n % 2 == 0:
        return n // 2
    else:
        return 3 * n + 1

def test_collatz_step():
    assert collatz_step(6) == 3, "even"
    assert collatz_step(3) == 10, "odd"

test_collatz_step()
