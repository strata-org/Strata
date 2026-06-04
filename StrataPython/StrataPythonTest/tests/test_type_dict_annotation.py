from typing import Dict

def test_type_dict_annotation():
    d: Dict[str, int] = {"a": 1}
    assert d["a"] == 1, "typed dict"

test_type_dict_annotation()
