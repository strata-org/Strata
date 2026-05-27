from typing import List

def linear_search(xs: List[int], target: int) -> int:
    i: int = 0
    n: int = len(xs)
    while i < n:
        if xs[i] == target:
            return i
        i = i + 1
    return -1

def main():
    xs: List[int] = [10, 20, 30, 40, 50]
    found: int = linear_search(xs, 30)
    assert found == 2, "30 is at index 2"
    missing: int = linear_search(xs, 99)
    assert missing == -1, "99 is not present"
