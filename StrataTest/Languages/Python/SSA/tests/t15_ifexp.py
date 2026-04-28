# Test: Ternary IfExp desugaring

cond: bool = True

# Simple IfExp
x = 1 if cond else 2

# Nested IfExp
y = "a" if cond else "b" if not cond else "c"

# IfExp in assignment
z: int = 10 if cond else 20
