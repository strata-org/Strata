from typing import Dict

class MyService:
    def known_method(self) -> int:
        return 1

def main():
    svc: MyService = MyService()
    svc.nonexistent_method()
