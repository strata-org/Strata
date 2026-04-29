import servicelib

def bad_method() -> bool:
    client = servicelib.connect("storage")
    client.nonexistent_method(Bucket="b", Key="k")
    return True
