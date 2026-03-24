import servicelib

def use_tuple_for() -> bool:
    client: Storage = servicelib.connect("storage")
    pairs: list = client.list_items(Bucket="mybucket")
    for k, v in pairs:
        client.put_item(Bucket="out", Key=k, Data=v)
    return True
