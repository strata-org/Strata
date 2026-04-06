from .Messaging import Messaging
from .Storage import Storage
from .Database import Database
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

@overload
def connect(
    service_name: Literal["database"],
) -> Database:
    ...
