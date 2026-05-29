# Test: passing a dispatch-created Composite value to a function with untyped parameter.
# Before the fix, this caused "Impossible to unify Any with Composite" because
# the factory dispatch produces a Composite-typed value but the function parameter
# defaults to Any.
import servicelib


def use_storage(client):
    client.put_item(Bucket="test", Key="k", Data="v")


use_storage(servicelib.connect("storage"))
