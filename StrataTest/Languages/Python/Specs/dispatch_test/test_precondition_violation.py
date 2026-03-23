import servicelib

def store_empty_bucket() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Bucket="", Key="mykey", Data="hello")
    return True
