# Duplicate @snapshot name= must be a hard error (names unique within a method).
@snapshot(lambda x: x, name="v0")
@snapshot(lambda x: x, name="v0")
def f(x: int) -> int:
    ...
