# Test: For loop (iterator protocol desugaring)

items = [1, 2, 3]

# Simple for
total: int = 0
for x in items:
    total += x

# For with break
for x in items:
    if x == 2:
        break

# For with continue
even_sum: int = 0
for x in items:
    if x % 2 != 0:
        continue
    even_sum += x
