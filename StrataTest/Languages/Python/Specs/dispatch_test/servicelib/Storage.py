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

class Storage:
    def put_item(self, **kwargs: Unpack[PutItemRequest]) -> None:
        ...
    def get_item(self, **kwargs: Unpack[GetItemRequest]) -> GetItemResponse:
        ...
    def delete_item(self, Bucket: str, Key: str) -> None:
        ...
    def list_items(self, **kwargs: Unpack[ListItemsRequest]) -> None:
        ...
