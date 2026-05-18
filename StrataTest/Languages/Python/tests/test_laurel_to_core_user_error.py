def helper() -> int:
    return 0

def main():
    assert helper() < helper() < 10, "chained compare with procedure calls"
