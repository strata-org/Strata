def main():
    i: int = 0
    seen: int = 0
    while i < 10:
        i = i + 1
        if i == 3:
            continue
        if i == 6:
            break
        seen = seen + 1
    assert seen == 4, "should have counted 1,2,4,5"
