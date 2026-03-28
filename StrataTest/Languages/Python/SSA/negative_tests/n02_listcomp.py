# Negative test: list comprehension → unsupported expression producing a value
# Expected: warning, unsupported instruction in place of comprehension

items = [1, 2, 3, 4, 5]
doubled = [x * 2 for x in items]
total = sum(doubled)
