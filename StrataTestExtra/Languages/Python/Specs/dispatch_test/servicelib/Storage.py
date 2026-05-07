from typing import TypedDict, Required, NotRequired, Unpack

PutItemRequest = TypedDict('PutItemRequest', {
    'Bucket': Required[str],
    'Key': Required[str],
    'Data': Required[str],
})

GetItemRequest = TypedDict('GetItemRequest', {
    'Bucket': Required[str],
    'Key': Required[str],
})

GetItemResponse = TypedDict('GetItemResponse', {
    'Data': NotRequired[str],
    'Found': NotRequired[bool],
})

ListItemsRequest = TypedDict('ListItemsRequest', {
    'Bucket': Required[str],
    'MaxResults': NotRequired[int],
    'NextToken': NotRequired[str],
})

@exhaustive
class Storage:
    def put_item(self, **kwargs: Unpack[PutItemRequest]) -> None:
        assert len(kwargs["Bucket"]) >= 1, "Bucket must not be empty"
        assert compile(r'^[a-z0-9-]+$').search(kwargs["Bucket"]) is not None, "Bucket must match ^[a-z0-9-]+$"
        assert len(kwargs["Key"]) >= 1, "Key must not be empty"
    def get_item(self, **kwargs: Unpack[GetItemRequest]) -> GetItemResponse:
        assert len(kwargs["Bucket"]) >= 1, "Bucket must not be empty"
        assert len(kwargs["Key"]) >= 1, "Key must not be empty"
    def delete_item(self, Bucket: str, Key: str) -> None:
        ...
    def list_items(self, **kwargs: Unpack[ListItemsRequest]) -> None:
        ...
