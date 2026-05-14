from typing import Any

class MyService:
    name: str

    def __init__(self, name: str) -> None:
        self.name = name

def create_service() -> Any:
    svc: MyService = MyService("test")
    return svc
