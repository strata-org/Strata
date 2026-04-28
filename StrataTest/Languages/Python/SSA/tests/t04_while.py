# Test: While, Break, Continue

# Simple while
i: int = 0
while i < 10:
    i += 1

# While with break
j: int = 0
while True:
    if j > 5:
        break
    j += 1

# While with continue
k: int = 0
total: int = 0
while k < 10:
    k += 1
    if k % 2 == 0:
        continue
    total += k
