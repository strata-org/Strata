from typing import List

def binary_search(xs: List[int], target: int) -> int:
    lo: int = 0
    hi: int = len(xs) - 1
    while lo <= hi:
        mid: int = (lo + hi) // 2
        if xs[mid] == target:
            return mid
        if xs[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1

def main():
    xs: List[int] = [1, 3, 5, 7, 9, 11, 13]
    found: int = binary_search(xs, 7)
    assert found == 3, "7 is at index 3"
    missing: int = binary_search(xs, 4)
    assert missing == -1, "4 is not present"
