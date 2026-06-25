import param_reassign_helper

def test_cross_module():
    r: int = param_reassign_helper.add_offset(5, offset=10)
    assert r == 15, "cross-module keyword call"

test_cross_module()
