# Test: tuple unpacking in for loops and assignments
def process_pairs(items: list) -> None:
    for k, v in items:
        print(k, v)

def use_enumerate(names: list) -> None:
    for i, name in enumerate(names):
        print(i, name)

def dict_iteration(d: dict) -> None:
    for key, value in d.items():
        print(key, value)

def tuple_assign() -> None:
    a, b = 1, 2
    x, y, z = a, b, a + b
    print(x, y, z)
