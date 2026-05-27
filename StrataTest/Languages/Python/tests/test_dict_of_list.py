from typing import Dict, List

def test():
    d: Dict[str, List[int]] = {"a": [1, 2]}
    assert d["a"][0] == 1, "dict of list"
test()
