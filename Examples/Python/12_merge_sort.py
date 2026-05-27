from typing import List

def merge(left: List[int], right: List[int]) -> List[int]:
    out: List[int] = []
    i: int = 0
    j: int = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            out = out + [left[i]]
            i = i + 1
        else:
            out = out + [right[j]]
            j = j + 1
    while i < len(left):
        out = out + [left[i]]
        i = i + 1
    while j < len(right):
        out = out + [right[j]]
        j = j + 1
    return out

def merge_sort(xs: List[int]) -> List[int]:
    n: int = len(xs)
    if n <= 1:
        return xs
    mid: int = n // 2
    left: List[int] = merge_sort(xs[:mid])
    right: List[int] = merge_sort(xs[mid:])
    return merge(left, right)

def main():
    xs: List[int] = [5, 2, 8, 1, 9, 3]
    sorted_xs: List[int] = merge_sort(xs)
    assert len(sorted_xs) == 6, "length preserved"
    assert sorted_xs[0] == 1, "first is 1"
    assert sorted_xs[5] == 9, "last is 9"
