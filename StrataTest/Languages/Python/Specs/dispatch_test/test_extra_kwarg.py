import servicelib

def extra_kwarg() -> bool:
    client = servicelib.connect("storage")
    client.get_item(Bucket="mybucket", Key="mykey", Bogus="unexpected")
    return True
