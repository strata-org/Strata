# Duplicate @ghost name= must be a hard error (names unique within a decl).
@ghost(name="g")
@ghost(name="g")
def f(x: int) -> int:
    ...
