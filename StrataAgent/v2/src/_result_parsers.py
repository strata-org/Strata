from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any, Generic, TypeVar

from pydantic import TypeAdapter

T = TypeVar("T")


class ResultParser(ABC, Generic[T]):
    @property
    @abstractmethod
    def name(self) -> str: ...

    @abstractmethod
    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None: ...

    def to_dict(self) -> dict[str, Any]:
        return {"type": self.name, **self._params()}

    def _params(self) -> dict[str, Any]:
        return {}


@dataclass
class JsonSchemaParser(ResultParser[T]):
    output_type: type[T]

    @property
    def name(self) -> str:
        return "json_schema"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        adapter = TypeAdapter(self.output_type)
        if structured_output is not None:
            return adapter.validate_python(structured_output)
        if raw_result:
            try:
                return adapter.validate_json(raw_result)
            except Exception:
                return None
        return None

    def get_output_format(self) -> dict[str, Any]:
        adapter = TypeAdapter(self.output_type)
        return {"type": "json_schema", "schema": adapter.json_schema()}

    def _params(self) -> dict[str, Any]:
        return {"output_type": self.output_type.__name__}


@dataclass
class RegexParser(ResultParser[dict[str, str]]):
    pattern: str
    flags: int = 0

    @property
    def name(self) -> str:
        return "regex"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> dict[str, str] | None:
        if not raw_result:
            return None
        match = re.search(self.pattern, raw_result, self.flags)
        if match:
            return match.groupdict()
        return None

    def _params(self) -> dict[str, Any]:
        return {"pattern": self.pattern}


@dataclass
class PydanticFromTextParser(ResultParser[T]):
    output_type: type[T]

    @property
    def name(self) -> str:
        return "pydantic_from_text"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        if not raw_result:
            return None
        adapter = TypeAdapter(self.output_type)
        json_match = re.search(r"```json\s*(.*?)\s*```", raw_result, re.DOTALL)
        text_to_parse = json_match.group(1) if json_match else raw_result
        try:
            return adapter.validate_json(text_to_parse)
        except Exception:
            return None

    def _params(self) -> dict[str, Any]:
        return {"output_type": self.output_type.__name__}


@dataclass
class CustomParser(ResultParser[T]):
    parse_fn: Any  # Callable[[str | None, Any | None], T | None]
    parser_name: str = "custom"

    @property
    def name(self) -> str:
        return self.parser_name

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        return self.parse_fn(raw_result, structured_output)

    def _params(self) -> dict[str, Any]:
        return {"parser_name": self.parser_name}


class RawTextParser(ResultParser[str]):
    @property
    def name(self) -> str:
        return "raw_text"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> str | None:
        return raw_result
