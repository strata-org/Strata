import myservice

def f():
    client = myservice.Client()
    result = client.nonexistent_method()
