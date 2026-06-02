# Test: a Composite-typed field (self.client: Storage) is passed to a function
# with an untyped parameter. The Composite is coerced to Any at the call site,
# but inside the class method where the field is used directly, dispatch still
# works because the field retains its Composite type.
import servicelib


class StorageUser:
    def __init__(self):
        self.client: Storage = servicelib.connect("storage")

    def do_put(self):
        self.client.put_item(Bucket="b", Key="k", Data="d")
