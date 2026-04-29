# Test: if/else control flow and type join at merge point
def f():
    if True:
        x = 1
    else:
        x = "hello"
    y = x
