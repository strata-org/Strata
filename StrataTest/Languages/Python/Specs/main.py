from re import compile
from basetypes import BaseClass
from typing import Any, Dict, List, Mapping, NotRequired, Sequence, TypedDict, Unpack

def dict_function(x : Dict[int, Any]):
    pass

def list_function(x : List[int]):
    pass

def sequence_function(x : Sequence[int]):
    pass

def base_function(x : BaseClass):
    pass

class MainClass:
    def main_method(self, x : BaseClass):
        pass

def main_function(x : MainClass):
    pass

def kwargs_function(**kw: int) -> Any:
    assert isinstance(kw["name"], str), 'Expected name to be str'
    assert kw["count"] >= 1, 'Expected count >= 1'

# Test f-string messages, regex, nested subscripts, and for-loops
TestRequest = TypedDict('TestRequest', {
    'Name': str,
    'Items': NotRequired[List[str]],
    'Tags': NotRequired[Mapping[str, str]],
})

def fstring_and_regex(**params: Unpack[TestRequest]) -> None:
    assert len(params["Name"]) >= 1, f'Expected len(params["Name"]) >= 1, got {len(params["Name"])}'
    assert len(params["Name"]) <= 100, f'Expected len(params["Name"]) <= 100, got {len(params["Name"])}'
    assert compile("^[a-zA-Z]+$").search(params["Name"]) is not None, f'params["Name"] did not match pattern'
    if "Items" in params:
        for item in params["Items"]:
            assert len(item) >= 1, f'Expected len(item) >= 1, got {len(item)}'
            assert len(item) <= 50, f'Expected len(item) <= 50, got {len(item)}'
    if "Tags" in params:
        for tag_key, tag_val in params["Tags"].items():
            assert len(tag_key) >= 1, f'Expected len(tag_key) >= 1, got {len(tag_key)}'

# Test float comparisons, negative int bounds, and __init__ class fields
FloatRequest = TypedDict('FloatRequest', {
    'SampleSize': NotRequired[float],
    'Score': NotRequired[float],
    'Count': NotRequired[int],
})

def float_and_negative_bounds(**fp: Unpack[FloatRequest]) -> None:
    # Float field with float literal bound
    if "Score" in fp:
        assert fp["Score"] >= 0.0, f'Expected Score >= 0.0'
        assert fp["Score"] <= 1.0, f'Expected Score <= 1.0'
    else:
        assert fp["SampleSize"] >= 0, f'Expected SampleSize >= 0 when no Score'
    # Float field with integer literal bound (the SampleSize pattern)
    if "SampleSize" in fp:
        assert fp["SampleSize"] >= 0, f'Expected SampleSize >= 0'
    # Float field with negative float bound
    if "Score" in fp:
        assert fp["Score"] >= -0.5, f'Expected Score >= -0.5'
    # Int field with negative bound
    if "Count" in fp:
        assert fp["Count"] >= -1, f'Expected Count >= -1'

class InnerHelper:
    pass

class ClassWithInit:
    def __init__(self):
        self.helper = self._InnerHelper()

    class _InnerHelper(InnerHelper):
        def do_work(self) -> None:
            pass
