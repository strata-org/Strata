import test_helper

# Test function inlining

def my_f(s: str) -> None:
    test_helper.procedure(s)

def main():
    my_f("foo")
    my_f("Foo")

if __name__ == "__main__":
    main()
