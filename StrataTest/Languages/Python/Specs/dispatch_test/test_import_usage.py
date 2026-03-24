import servicelib
import sys

def use_import() -> bool:
    client: Storage = servicelib.connect("storage")
    name: str = sys.argv[1]
    client.put_item(Bucket="b", Key=name, Data="v")
    return True
