import servicelib

def dict_expand_call() -> bool:
    client = servicelib.connect("storage")
    params: dict[str, str] = {"Bucket": "mybucket", "Key": "mykey", "Data": "hello"}
    client.put_item(**params)
    return True
