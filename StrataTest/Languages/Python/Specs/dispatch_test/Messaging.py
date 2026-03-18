from typing import TypedDict, Required, NotRequired, Unpack

SendRequest = TypedDict('SendRequest', {
    'Topic': Required[str],
    'Body': Required[str],
})

ReceiveResponse = TypedDict('ReceiveResponse', {
    'Body': NotRequired[str],
    'Id': NotRequired[str],
})

class Messaging:
    def send(self, **kwargs: Unpack[SendRequest]) -> None:
        ...
    def receive(self, Topic: str) -> ReceiveResponse:
        ...
