from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any


class HaltValidator(ABC):
    @property
    @abstractmethod
    def name(self) -> str: ...

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return False

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return False

    def to_dict(self) -> dict[str, Any]:
        return {"type": self.name, **self._params()}

    def _params(self) -> dict[str, Any]:
        return {}


@dataclass
class ContainsText(HaltValidator):
    text: str
    case_sensitive: bool = True

    @property
    def name(self) -> str:
        return "contains_text"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        target = self.text if self.case_sensitive else self.text.lower()
        for msg in messages:
            content = str(msg)
            if not self.case_sensitive:
                content = content.lower()
            if target in content:
                return True
        return False

    def _params(self) -> dict[str, Any]:
        return {"text": self.text, "case_sensitive": self.case_sensitive}


@dataclass
class MessageCount(HaltValidator):
    max_messages: int

    @property
    def name(self) -> str:
        return "message_count"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return len(messages) >= self.max_messages

    def _params(self) -> dict[str, Any]:
        return {"max_messages": self.max_messages}


@dataclass
class ResultFieldEquals(HaltValidator):
    field_name: str
    expected_value: Any

    @property
    def name(self) -> str:
        return "result_field_equals"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        if parsed_result is None:
            return False
        if isinstance(parsed_result, dict):
            return parsed_result.get(self.field_name) == self.expected_value
        return getattr(parsed_result, self.field_name, None) == self.expected_value

    def _params(self) -> dict[str, Any]:
        return {"field_name": self.field_name, "expected_value": self.expected_value}


@dataclass
class ResultFieldTruthy(HaltValidator):
    field_name: str

    @property
    def name(self) -> str:
        return "result_field_truthy"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        if parsed_result is None:
            return False
        if isinstance(parsed_result, dict):
            return bool(parsed_result.get(self.field_name))
        return bool(getattr(parsed_result, self.field_name, None))

    def _params(self) -> dict[str, Any]:
        return {"field_name": self.field_name}


@dataclass
class ResultTextContains(HaltValidator):
    text: str

    @property
    def name(self) -> str:
        return "result_text_contains"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return raw_result is not None and self.text in raw_result

    def _params(self) -> dict[str, Any]:
        return {"text": self.text}


@dataclass
class AnyOf(HaltValidator):
    validators: list[HaltValidator] = field(default_factory=list)

    @property
    def name(self) -> str:
        return "any_of"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return any(v.should_halt_on_messages(messages) for v in self.validators)

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return any(v.should_halt_on_result(parsed_result, raw_result) for v in self.validators)

    def _params(self) -> dict[str, Any]:
        return {"validators": [v.to_dict() for v in self.validators]}


@dataclass
class AllOf(HaltValidator):
    validators: list[HaltValidator] = field(default_factory=list)

    @property
    def name(self) -> str:
        return "all_of"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return all(v.should_halt_on_messages(messages) for v in self.validators)

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return all(v.should_halt_on_result(parsed_result, raw_result) for v in self.validators)

    def _params(self) -> dict[str, Any]:
        return {"validators": [v.to_dict() for v in self.validators]}
