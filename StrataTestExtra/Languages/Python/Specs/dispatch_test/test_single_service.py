import servicelib

def store_data() -> bool:
    client = servicelib.connect("storage")
    client.put_item(Bucket="mybucket", Key="mykey", Data="hello")
    result = client.get_item(Bucket="mybucket", Key="mykey")
    return True
