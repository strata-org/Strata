from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Tool:
    name: str
    pattern: str | None = None

    def to_claude_format(self) -> str:
        if self.pattern:
            return f"{self.name}({self.pattern})"
        return self.name


@dataclass
class ToolSet:
    allowed: list[Tool] = field(default_factory=list)
    disallowed: list[Tool] = field(default_factory=list)

    def allow(self, name: str, pattern: str | None = None) -> ToolSet:
        self.allowed.append(Tool(name=name, pattern=pattern))
        return self

    def disallow(self, name: str, pattern: str | None = None) -> ToolSet:
        self.disallowed.append(Tool(name=name, pattern=pattern))
        return self

    def to_claude_allowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.allowed]

    def to_claude_disallowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.disallowed]

    @classmethod
    def from_names(cls, *names: str) -> ToolSet:
        return cls(allowed=[Tool(name=n) for n in names])
