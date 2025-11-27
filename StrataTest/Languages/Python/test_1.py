import test_helper

# Test function defs

def my_f(s: str) -> None:
    test_helper.procedure(s)

def main():
    my_f("foo")

if __name__ == "__main__":
    main()
