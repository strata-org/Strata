import test_helper


def main():
    # Test minimal precondition verification

    # Should succeed
    test_helper.procedure("foo", opt_name = None)

    # Should succeed
    test_helper.procedure("foo", opt_name = "bar")

    # Should error
    test_helper.procedure("Foo", opt_name = None)

    # Should error
    test_helper.procedure("foo", opt_name = "Bar")

if __name__ == "__main__":
    main()