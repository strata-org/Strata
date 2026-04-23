src: int = 100
dst: int = 0

def copy_src_to_dst() -> None:
    global src, dst
    dst = src

def main() -> None:
    global src, dst
    copy_src_to_dst()
    assert dst == 100
    assert src == 100
