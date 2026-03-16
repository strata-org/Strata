company = {
    "engineering": {
        "backend": {"lead": "Alice", "members": ["David", "Eve", "Frank"]},
        "frontend": {"lead": "Bob", "members": ["Charlie", "Diana", "Frank"]}
    },
    "sales": {
        "north": {"lead": "Charlie", "members": 4},
        "south": {"lead": "Diana", "members": 6}
    }
}

company["engineering"]["frontend"]["members"][0] = "Peter"

company["management"] = {"CEO": "Grant"}

assert company["engineering"]["frontend"]["members"][0] == "Peter"

assert "Frank" in company["engineering"]["frontend"]["members"]

assert "management" in company


# Slice tests
numbers = [1, 2, 3, 4, 5]

# Slice with lower bound only
tail = numbers[1:]
assert tail != None

# Slice with upper bound only
head = numbers[:3]
assert head != None

# Slice with both bounds
middle = numbers[1:4]
assert middle != None
