# Test: Attribute access (getattr), setAttr

class Config:
    def __init__(self):
        self.debug = False
        self.level = 0

c = Config()

# Attribute read
flag = c.debug

# Attribute write
c.debug = True
c.level = 5

# Chained attribute access
class Inner:
    def __init__(self):
        self.value = 42

class Outer:
    def __init__(self):
        self.inner = Inner()

o = Outer()
v = o.inner.value
