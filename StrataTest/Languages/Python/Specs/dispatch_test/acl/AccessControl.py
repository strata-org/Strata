from typing import TypedDict, Required, Unpack

ReadRequest = TypedDict('ReadRequest', {
    'role': Required[str],
    'resource_id': Required[str],
})

WriteRequest = TypedDict('WriteRequest', {
    'role': Required[str],
    'resource_id': Required[str],
    'content': Required[str],
})

DeleteRequest = TypedDict('DeleteRequest', {
    'role': Required[str],
    'resource_id': Required[str],
})

@exhaustive
class AccessControl:
    def read_resource(self, **kwargs: Unpack[ReadRequest]) -> None:
        assert kwargs["role"] == "admin" or kwargs["role"] == "editor" or kwargs["role"] == "viewer"
        assert len(kwargs["resource_id"]) >= 1

    def write_resource(self, **kwargs: Unpack[WriteRequest]) -> None:
        assert kwargs["role"] == "admin" or kwargs["role"] == "editor"
        assert len(kwargs["resource_id"]) >= 1

    def delete_resource(self, **kwargs: Unpack[DeleteRequest]) -> None:
        assert kwargs["role"] == "admin"
        assert len(kwargs["resource_id"]) >= 1
