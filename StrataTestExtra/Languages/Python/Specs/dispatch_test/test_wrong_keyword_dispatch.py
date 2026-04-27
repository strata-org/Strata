import servicelib

def wrong_keyword() -> bool:
    client = servicelib.connect(wrong_param="storage")
    result = client.get_item(Bucket="mybucket", Key="mykey")
    return True
