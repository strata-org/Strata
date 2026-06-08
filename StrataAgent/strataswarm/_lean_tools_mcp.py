"""MCP server exposing SwarmLeanTools to agents.

Provides verified file operations (write_decomposed_lemma, refactor_file,
count_sorries, etc.) as MCP tools that agents can call directly.

The server wraps the Python SwarmLeanTools singleton — agents never interact
with the Lean process directly.
"""

from __future__ import annotations

import json
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool


def create_lean_tools_server(workspace: str | None = None):
    """Create an MCP server exposing lean analysis and file tools.

    Args:
        workspace: If set, write operations are restricted to this workspace.
                   Read operations (count_sorries, list_theorems) work on any file.
    """
    from .modules.po_lean import get_lean_tools

    @tool(
        name="write_decomposed_lemma",
        description=(
            "Write a single decomposed lemma to a file with verification. "
            "Enforces: (1) exactly one theorem in the file, (2) theorem name matches, "
            "(3) file compiles. Returns the created file path or an error. "
            "File is named: lemma_helper_<theorem_name>.lean"
        ),
        input_schema={
            "type": "object",
            "properties": {
                "file_content": {
                    "type": "string",
                    "description": "Full Lean file content (imports + theorem statement + sorry body)",
                },
                "theorem_name": {
                    "type": "string",
                    "description": "The theorem name (must match the theorem in file_content)",
                },
            },
            "required": ["file_content", "theorem_name"],
        },
    )
    async def write_decomposed_lemma(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        content = input["file_content"]
        name = input["theorem_name"]

        if not workspace:
            return {"content": [{"type": "text", "text": json.dumps({"error": "no workspace configured"})}]}

        output_dir = f"{workspace}/decomposed"
        result = tools.write_decomposed_lemma(content, name, output_dir)

        if result.error:
            return {"content": [{"type": "text", "text": json.dumps({
                "success": False, "error": result.error,
            })}]}

        return {"content": [{"type": "text", "text": json.dumps({
            "success": True,
            "file_path": result.file_path,
            "theorem_name": result.theorem_name,
            "has_sorry": result.has_sorry,
        })}]}

    @tool(
        name="count_sorries",
        description=(
            "Count sorry occurrences in a Lean file. "
            "Returns total count and list of theorem names that contain sorry."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "file_path": {
                    "type": "string",
                    "description": "Relative path from project root",
                },
            },
            "required": ["file_path"],
        },
    )
    async def count_sorries(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        result = tools.count_sorries(input["file_path"])
        return {"content": [{"type": "text", "text": json.dumps({
            "total": result.total,
            "sorry_decls": result.sorry_decls,
            "error": result.error,
        })}]}

    @tool(
        name="list_theorems",
        description=(
            "List all theorems in a Lean file with their sorry/proved status."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "file_path": {
                    "type": "string",
                    "description": "Relative path from project root",
                },
            },
            "required": ["file_path"],
        },
    )
    async def list_theorems(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        result = tools.list_theorems(input["file_path"])
        return {"content": [{"type": "text", "text": json.dumps({
            "theorems": [{"name": t.name, "status": t.status} for t in result.theorems],
            "error": result.error,
        })}]}

    @tool(
        name="check_imports",
        description="List all import statements in a Lean file.",
        input_schema={
            "type": "object",
            "properties": {
                "file_path": {
                    "type": "string",
                    "description": "Relative path from project root",
                },
            },
            "required": ["file_path"],
        },
    )
    async def check_imports(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        result = tools.check_imports(input["file_path"])
        return {"content": [{"type": "text", "text": json.dumps({
            "imports": result.imports,
            "error": result.error,
        })}]}

    return create_sdk_mcp_server(
        name="lean_tools",
        version="1.0.0",
        tools=[write_decomposed_lemma, count_sorries, list_theorems, check_imports],
    )
