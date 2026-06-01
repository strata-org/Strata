import servicelib

def dict_expand_with_optional() -> bool:
    client = servicelib.connect("storage")
    params: dict[str, str] = {"Bucket": "mybucket"}
    client.list_items(**params)
    return True
