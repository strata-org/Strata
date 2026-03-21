from typing import TypedDict, Required, NotRequired, Unpack

SendRequest = TypedDict('SendRequest', {
    'url': Required[str],
    'body': Required[str],
    'timeout': NotRequired[int],
})

class MessageService:
    def send(self, **kwargs: Unpack[SendRequest]) -> None:
        assert len(kwargs["url"]) >= 1, f'url must not be empty'
        assert len(kwargs["url"]) <= 256, f'url too long'
        assert len(kwargs["body"]) >= 1, f'body must not be empty'
