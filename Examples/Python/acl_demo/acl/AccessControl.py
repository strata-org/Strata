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

class AccessControl:
    def read_resource(self, **kwargs: Unpack[ReadRequest]) -> None:
        assert kwargs["role"] == "admin" or kwargs["role"] == "editor" or kwargs["role"] == "viewer", "role has read permission"
        assert len(kwargs["resource_id"]) >= 1, "resource_id is non-empty"

    def write_resource(self, **kwargs: Unpack[WriteRequest]) -> None:
        assert kwargs["role"] == "admin" or kwargs["role"] == "editor", "role has write permission"
        assert len(kwargs["resource_id"]) >= 1, "resource_id is non-empty"

    def delete_resource(self, **kwargs: Unpack[DeleteRequest]) -> None:
        assert kwargs["role"] == "admin", "role has delete permission"
        assert len(kwargs["resource_id"]) >= 1, "resource_id is non-empty"
