import servicelib

class ClientHolder:
    def __init__(self):
        self.client: Storage = servicelib.connect("storage")

    def get_client_name(self) -> str:
        return self.client
