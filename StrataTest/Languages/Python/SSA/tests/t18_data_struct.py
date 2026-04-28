# Test: Dict, List, Tuple, Subscript, Slice

# List
nums = [1, 2, 3, 4, 5]
first = nums[0]
nums[0] = 10
sliced = nums[1:3]

# Dict
d = {"a": 1, "b": 2}
val = d["a"]
d["c"] = 3

# Tuple
t = (1, "two", 3.0)
elem = t[0]

# Slice with step
every_other = nums[::2]
