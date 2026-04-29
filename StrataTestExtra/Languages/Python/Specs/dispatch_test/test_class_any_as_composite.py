import servicelib

class ClientHolder:
    def __init__(self, name: str):
        self.client: Storage = name
