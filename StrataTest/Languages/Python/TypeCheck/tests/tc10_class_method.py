import myservice

def f():
    client = myservice.Client()
    result = client.get_item(key="abc")
