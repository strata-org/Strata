import test_helper

# Test minimal precondition verification

# Should succeed
test_helper.procedure("foo")

# Should succeed
test_helper.procedure("foo", opt_name = "bar")

# Should error
test_helper.procedure("Foo")

# Should error
test_helper.procedure("foo", opt_name = "Bar")