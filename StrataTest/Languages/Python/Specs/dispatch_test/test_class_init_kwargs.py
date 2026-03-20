import servicelib

class MyClient:
    region: str

    def __init__(self, region: str = "us-east-1") -> None:
        self.region = region

def use_class_init_kwargs() -> bool:
    client: MyClient = MyClient(region="us-west-2")
    return True
