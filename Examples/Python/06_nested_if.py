def main():
    x: int = 5
    label: int = 0
    if x > 0:
        if x < 10:
            label = 1
        else:
            label = 2
    else:
        label = 3
    assert label == 1, "label should be 1"
