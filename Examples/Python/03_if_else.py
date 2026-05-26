def main():
    flag: bool = True
    val: int = 0
    if flag:
        val = 10
    else:
        val = 20
    assert val == 10, "val should be 10"
