# Test: passing a dispatch-created Composite value as a positional argument
# alongside **kwargs expansion. This exercises the first coerceArgsToAny call
# site (the isVarKwargs branch) where positional args precede the dict expansion.
import servicelib


def use_client(client, Bucket, Key, Data):
    client.put_item(Bucket=Bucket, Key=Key, Data=Data)


def call_with_kwargs():
    extra = {"Bucket": "b", "Key": "k", "Data": "v"}
    use_client(servicelib.connect("storage"), **extra)
