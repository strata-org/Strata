from Storage import Storage
from Messaging import Messaging
from typing import Literal, overload

@overload
def connect(
    service_name: Literal["storage"],
) -> Storage:
    ...

@overload
def connect(
    service_name: Literal["messaging"],
) -> Messaging:
    ...
