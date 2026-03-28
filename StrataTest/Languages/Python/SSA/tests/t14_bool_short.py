# Test: and/or short-circuit desugaring

a: bool = True
b: bool = False

# and: short-circuits on False
r1 = a and b

# or: short-circuits on True
r2 = a or b

# Nested
r3 = a and b or a

# With non-bool values (Python truthy semantics)
x = 0 or 42
y = "hello" and "world"
