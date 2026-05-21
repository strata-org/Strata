from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

_TOOL_PATTERN_RE = re.compile(r"^(\w+)\((.+)\)$")
_FILE_TOOLS = {"Read", "Edit", "Write"}


def _resolve_path_pattern(name: str, pattern: str, base_dir: Path | None) -> str:
    """Resolve a relative path pattern to absolute for file-oriented tools."""
    if base_dir is None:
        return pattern
    if name not in _FILE_TOOLS:
        return pattern
    if pattern.startswith("/"):
        return pattern
    resolved = str(base_dir / pattern)
    return resolved


def parse_tool_string(tool_str: str, base_dir: Path | None = None) -> Tool:
    """Parse 'ToolName(path_pattern)' or 'ToolName' into a Tool with resolved paths."""
    m = _TOOL_PATTERN_RE.match(tool_str)
    if m:
        name = m.group(1)
        pattern = m.group(2)
        resolved = _resolve_path_pattern(name, pattern, base_dir)
        return Tool(name=name, pattern=resolved)
    return Tool(name=tool_str)


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

    def allow(self, tool_str: str, base_dir: Path | None = None) -> ToolSet:
        self.allowed.append(parse_tool_string(tool_str, base_dir))
        return self

    def disallow(self, tool_str: str, base_dir: Path | None = None) -> ToolSet:
        self.disallowed.append(parse_tool_string(tool_str, base_dir))
        return self

    def to_claude_allowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.allowed]

    def to_claude_disallowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.disallowed]

    @classmethod
    def from_names(cls, *names: str) -> ToolSet:
        return cls(allowed=[Tool(name=n) for n in names])
