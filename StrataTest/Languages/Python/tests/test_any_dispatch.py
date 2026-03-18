# Test case: Any values that cannot be constant-evaluated to a single type.
# When flag is True, x is from_int(42); when False, x is from_string("hello").
# At the merge point after the if/else, x has unknown constructor —
# partial evaluation must NOT simplify tester/selector applications on x.

def main():
    # Case 1: Concrete — partial eval should simplify completely
    a: int = 3
    b: int = 4
    c: int = a + b
    assert c == 7, "concrete add failed"

    # Case 2: Conditional assignment — x's type depends on runtime value
    flag: bool = True
    x: int = 0
    if flag:
        x = 42
    else:
        x = 99
    # x is from_int but the value is not statically known after the merge
    assert x == 42, "conditional value"

if __name__ == "__main__":
    main()
