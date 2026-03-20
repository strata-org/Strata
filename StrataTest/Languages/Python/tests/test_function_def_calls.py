import test_helper

# Test function defs

def my_f(s: str):
    test_helper.procedure(s, opt_name = None)

def main():
    my_f("foo")

if __name__ == "__main__":
    main()
