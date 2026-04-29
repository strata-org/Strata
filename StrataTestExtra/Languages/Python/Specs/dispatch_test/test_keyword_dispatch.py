import servicelib

def keyword_dispatch() -> bool:
    client = servicelib.connect(service_name="storage")
    result = client.get_item(Bucket="mybucket", Key="mykey")
    return True
