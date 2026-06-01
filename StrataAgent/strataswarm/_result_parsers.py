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


_PRIMITIVE_TYPES = (bool, int, float, str)


@dataclass
class JsonSchemaParser(ResultParser[T]):
    output_type: type[T]

    @property
    def name(self) -> str:
        return "json_schema"

    @property
    def _is_primitive(self) -> bool:
        return self.output_type in _PRIMITIVE_TYPES

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        adapter = TypeAdapter(self.output_type)
        # For primitives, unwrap from {"value": ...} wrapper
        if self._is_primitive:
            if structured_output is not None and isinstance(structured_output, dict):
                structured_output = structured_output.get("value")
            elif raw_result:
                try:
                    import json
                    wrapped = json.loads(raw_result)
                    if isinstance(wrapped, dict) and "value" in wrapped:
                        return adapter.validate_python(wrapped["value"])
                except Exception:
                    pass
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
        schema = adapter.json_schema()
        # Primitives need wrapping in an object for the API
        if self._is_primitive:
            schema = {
                "type": "object",
                "properties": {"value": schema},
                "required": ["value"],
            }
        return {"type": "json_schema", "schema": schema}

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
