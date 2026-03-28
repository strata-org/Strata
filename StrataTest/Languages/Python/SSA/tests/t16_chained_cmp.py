# Test: Chained comparison desugaring (a < b < c -> (a < b) and (b < c))

x: int = 5
y: int = 10
z: int = 15

# Two-way chain
r1 = x < y < z

# Three-way chain
r2 = 0 < x < y < z

# Mixed operators
r3 = x <= y < z
r4 = x < y >= z
