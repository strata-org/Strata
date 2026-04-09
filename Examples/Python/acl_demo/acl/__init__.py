from .AccessControl import AccessControl
from typing import Literal, overload

@overload
def connect(
    service_name: Literal["access_control"],
) -> AccessControl:
    ...
