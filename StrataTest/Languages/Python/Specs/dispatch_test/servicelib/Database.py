from typing import TypedDict, Required, NotRequired, Unpack

QueryRequest = TypedDict('QueryRequest', {
    'Table': Required[str],
    'Key': Required[str],
})

class DatabaseError(Exception):
    response: dict

class Database:
    # Nested exception container — mimics boto3 service client pattern.
    # The pyspec compiler emits _Exceptions as a subclass in the Ion file,
    # but ToLaurel does not translate subclasses, so the field type
    # "servicelib_Database__Exceptions" is undefined after translation.
    class _Exceptions:
        DatabaseError = DatabaseError

    def __init__(self) -> None:
        self.exceptions = self._Exceptions()

    def query(self, **kwargs: Unpack[QueryRequest]) -> str:
        assert len(kwargs["Table"]) >= 1, "Table must not be empty"
        assert len(kwargs["Key"]) >= 1, "Key must not be empty"
