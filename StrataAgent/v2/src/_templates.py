from __future__ import annotations

from pathlib import Path
from typing import Any

from jinja2 import Environment, FileSystemLoader, Template


def render_prompt(prompt: str | Path, variables: dict[str, Any]) -> str:
    if isinstance(prompt, Path) or (
        isinstance(prompt, str) and (prompt.endswith(".j2") or prompt.endswith(".jinja2"))
    ):
        path = Path(prompt)
        if path.exists():
            env = Environment(loader=FileSystemLoader(str(path.parent)))
            tmpl = env.get_template(path.name)
            return tmpl.render(**variables)
        raise FileNotFoundError(f"Template not found: {path}")

    if isinstance(prompt, str) and ("{{" in prompt or "{%" in prompt):
        tmpl = Template(prompt)
        return tmpl.render(**variables)

    return str(prompt)
