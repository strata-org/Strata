"""Compile-check MCP for the BigSur repair agent.

BigSur rewrites contracts across the Sandbox, then must confirm the files it
touched still COMPILE before it attests a repair is consistent. The lean-lsp MCP
tools it is otherwise given (`lean_diagnostic_messages`) cannot deliver that
verdict after a CROSS-FILE edit: once BigSur edits a child, the parent's imports go
"out of date" and diagnostics return a rebuild signal, not a pass/fail. And the
lean-lsp `lean_build`/`lean_verify` tools choke on this repo's `module` files.

So BigSur gets the SAME build the ASSEMBLY phase uses: a direct `lake build` that
rebuilds oleans (clearing the stale-import problem by construction) and reports
genuine `": error:"` diagnostics. The tool takes a FILE PATH — BigSur chooses which
file to build (the child it just edited, then the parent) — and converts it to the
module name `lake build` expects. This server is non-destructive (read/verify
only); it is kept separate from the destructive ledger/snapshot MCPs.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from .modules.po_lean import lake_build, file_path_to_module, LEAN_BUILD_TIMEOUT


def create_bigsur_build_mcp_server(cwd: Path):
    """Create the lake-build compile-check MCP for BigSur.

    Args:
        cwd: the project root (contains lakefile.toml) — `lake build` runs here and
             file paths are resolved relative to it.
    """
    cwd = Path(cwd)

    def _text(payload: Any) -> dict[str, Any]:
        return {"content": [{"type": "text",
                             "text": json.dumps(payload, indent=2) if not isinstance(payload, str) else payload}]}

    # NOTE: the tool is named `lake_build_check`, NOT `lean_build`. The short (final
    # `__`-segment) name must be UNIQUE: the runtime block hook matches on that bare
    # segment, so if this tool were also called `lean_build` it would collide with
    # the lean-lsp `mcp__lean_lsp__lean_build` (blocked for BigSur) — blocking one by
    # short name would silently kill the other. A distinct segment avoids that.
    @tool(
        name="lake_build_check",
        description=(
            "Compile a Lean file with `lake build` and report whether it succeeds. "
            "Pass the FILE PATH you want built (e.g. the child you just edited, then "
            "its parent) — relative to the project root or absolute under it; the "
            "tool converts it to the module name for you. This REBUILDS oleans, so it "
            "is the correct way to verify a cross-file edit: after you change a child, "
            "`lean_diagnostic_messages` on the parent only reports 'imports out of "
            "date' (a rebuild signal, NOT a verdict), whereas this gives a real "
            "pass/fail. Returns {ok, errors}: ok=true means no `error:` diagnostics "
            "(sorry warnings are fine). Use this to confirm each file you touched "
            "compiles before you attest the repair is done."),
        input_schema={
            "type": "object",
            "properties": {
                "file_path": {
                    "type": "string",
                    "description": "Path to the .lean file to build (or a module name)."},
            },
            "required": ["file_path"],
        },
    )
    async def lake_build_check(input: dict[str, Any]) -> dict[str, Any]:
        module = file_path_to_module(input["file_path"], cwd)
        ok, errors = lake_build(module, cwd, timeout=LEAN_BUILD_TIMEOUT)
        return _text({
            "module": module,
            "ok": ok,
            "error_count": len(errors),
            "errors": errors[:40],
        })

    return create_sdk_mcp_server(
        name="bigsur_build",
        version="1.0.0",
        tools=[lake_build_check],
    )
