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

    @tool(
        name="show_file_state",
        description=(
            "Get complete proof state of a Lean file: all theorems with sorry/proved status, "
            "whether it compiles, and which is the main theorem."
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
    async def show_file_state(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        result = tools.show_file_state(input["file_path"])
        return {"content": [{"type": "text", "text": json.dumps(result, indent=2)}]}

    @tool(
        name="write_helper_lemma",
        description=(
            "Create a helper lemma file AND replace a sorry in the target file with a tactic "
            "that uses the helper. TRANSACTIONAL: if anything fails (helper doesn't compile, "
            "replacement doesn't type-check), everything is reverted.\n\n"
            "The tool: (1) writes helper to decomposed/, (2) builds it, (3) adds import to target, "
            "(4) replaces sorry at the given line/col with the replacement tactic, (5) verifies target compiles."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "theorem_name": {
                    "type": "string",
                    "description": "Name of the helper theorem (must match the theorem in theorem_statement)",
                },
                "theorem_statement": {
                    "type": "string",
                    "description": "Full Lean theorem statement with sorry body (e.g. 'theorem foo (x : Nat) : x > 0 := by sorry')",
                },
                "additional_imports": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Extra import lines the helper needs (e.g. ['import Strata.DL.Imperative.SemanticsProps'])",
                },
                "sorry_line": {
                    "type": "integer",
                    "description": "0-indexed line number of the sorry to replace in the target file",
                },
                "sorry_col": {
                    "type": "integer",
                    "description": "Column number of the sorry",
                },
                "replacement_tactic": {
                    "type": "string",
                    "description": "Tactic to replace sorry with (e.g. 'exact helper_name x h')",
                },
            },
            "required": ["theorem_name", "theorem_statement", "additional_imports", "sorry_line", "sorry_col", "replacement_tactic"],
        },
    )
    async def write_helper_lemma_tool(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()

        if not workspace:
            return {"content": [{"type": "text", "text": json.dumps({"error": "no workspace configured"})}]}

        # Determine target file (Stub.lean in workspace)
        target_file = f"{workspace}/Stub.lean"

        result = tools.write_helper_lemma(
            theorem_name=input["theorem_name"],
            theorem_statement=input["theorem_statement"],
            additional_imports=input.get("additional_imports", []),
            sorry_line=input["sorry_line"],
            sorry_col=input["sorry_col"],
            replacement_tactic=input["replacement_tactic"],
            target_file=target_file,
            workspace=workspace,
        )

        if result.error:
            return {"content": [{"type": "text", "text": json.dumps({
                "success": False, "error": result.error,
            })}]}

        return {"content": [{"type": "text", "text": json.dumps({
            "success": True,
            "file_path": result.file_path,
            "theorem_name": result.theorem_name,
        })}]}

    @tool(
        name="get_sorry_positions",
        description=(
            "Get all sorry positions in a Lean file (line and column, 0-indexed). "
            "Comment-aware — ignores sorry in comments. Use this to know WHERE to "
            "call lean_goal for each sorry."
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
    async def get_sorry_positions(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        positions = tools.get_sorry_positions(input["file_path"])
        return {"content": [{"type": "text", "text": json.dumps({"positions": positions})}]}

    @tool(
        name="get_sorries_by_theorem",
        description=(
            "Get sorry positions grouped by theorem. Shows which theorems have sorry "
            "and exactly where each sorry is (line, col). Optionally filter by theorem names."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "file_path": {
                    "type": "string",
                    "description": "Relative path from project root",
                },
                "filter_names": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Only include these theorem names (omit for all)",
                },
            },
            "required": ["file_path"],
        },
    )
    async def get_sorries_by_theorem(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        result = tools.get_sorries_by_theorem(
            input["file_path"],
            filter_names=input.get("filter_names"),
        )
        return {"content": [{"type": "text", "text": json.dumps(result, indent=2)}]}

    @tool(
        name="collect_progress",
        description=(
            "Recursively collect all progress.md files under the workspace. "
            "Returns a summary of all PO activity across the entire proof tree, "
            "plus the most recently modified .lean file to detect active work."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {
                    "type": "string",
                    "description": "Workspace path (e.g. 'StrataAgent/Sandbox')",
                },
            },
            "required": ["workspace"],
        },
    )
    async def collect_progress_tool(input: dict[str, Any]) -> dict[str, Any]:
        from .modules.po_util import collect_progress
        result = collect_progress(input["workspace"])
        return {"content": [{"type": "text", "text": result}]}

    return create_sdk_mcp_server(
        name="lean_tools",
        version="1.0.0",
        tools=[write_decomposed_lemma, count_sorries, list_theorems,
               check_imports, show_file_state, write_helper_lemma_tool,
               get_sorry_positions, get_sorries_by_theorem, collect_progress_tool],
    )


def create_extractor_mcp_server(session: "MoveSession"):
    """Create an MCP server with extraction tools bound to a MoveSession.

    Tools:
      - get_declarations: see all declarations in the file
      - move_decl: register a declaration to be moved to its own file
      - commit: execute all moves, rewrite Stub.lean, build, verify
      - revert: undo everything, back to original for retry
    """
    from .modules.po_lean import MoveSession

    @tool(
        name="get_declarations",
        description="Get all declarations in the file. Shows name, type, sorry status, mutual groups, and which is the main theorem.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def get_declarations_tool(input: dict[str, Any]) -> dict[str, Any]:
        decls = session.get_declarations()
        return {"content": [{"type": "text", "text": json.dumps(decls, indent=2)}]}

    @tool(
        name="move_decl",
        description=(
            "Register a declaration to be moved to its own file. "
            "Specify which other declarations it depends on (that are also being moved) as additional_imports. "
            "Mutual group members are moved together automatically. "
            "Do NOT move the main theorem."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "decl_name": {"type": "string", "description": "Name of the declaration to move"},
                "additional_imports": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Names of other declarations this one depends on (local deps only, not library imports)",
                },
            },
            "required": ["decl_name"],
        },
    )
    async def move_decl_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.move_decl(input["decl_name"], input.get("additional_imports", []))
        return {"content": [{"type": "text", "text": result}]}

    @tool(
        name="commit",
        description=(
            "Execute all registered moves: write decomposed files, rewrite Stub.lean "
            "(header + imports + main theorem only), build everything, verify Stub.lean "
            "compiles sorry-free. Returns success or error."
        ),
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def commit_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.commit()
        if result.error:
            return {"content": [{"type": "text", "text": f"FAILED: {result.error}"}]}
        return {"content": [{"type": "text", "text": f"SUCCESS: {len(result.created_files)} files created, Stub.lean compiles sorry-free"}]}

    @tool(
        name="revert",
        description="Undo everything: restore original Stub.lean, remove decomposed files. Use this after a failed commit to retry with different moves.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def revert_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.revert()
        return {"content": [{"type": "text", "text": result}]}

    @tool(
        name="move_lines",
        description=(
            "Move lines start-end (1-indexed, inclusive) from Stub.lean into lemma_helper_<name>.lean. "
            "Use this when move_decl fails (e.g. for set_option...in mutual blocks, or complex declarations). "
            "The agent reads the file, identifies the exact line range, and moves it. "
            "IMPORTANT: Move entire mutual blocks together (from 'mutual' or 'set_option' to 'end')."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "start": {"type": "integer", "description": "Start line (1-indexed, inclusive)"},
                "end": {"type": "integer", "description": "End line (1-indexed, inclusive)"},
                "name": {"type": "string", "description": "Name for the helper (creates lemma_helper_<name>.lean)"},
            },
            "required": ["start", "end", "name"],
        },
    )
    async def move_lines_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.move_lines(input["start"], input["end"], input["name"])
        return {"content": [{"type": "text", "text": result}]}

    @tool(
        name="add_imports",
        description=(
            "Add imports to lemma_helper_<name>.lean. "
            "Pass helper names (e.g. 'detBlockSim') — they resolve to the correct module path automatically. "
            "Or pass full module paths (e.g. 'StrataAgent.Sandbox.Stub.Def')."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "imports": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Helper names or full module paths to import",
                },
                "name": {"type": "string", "description": "Target helper name (the file to add imports to)"},
            },
            "required": ["imports", "name"],
        },
    )
    async def add_imports_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.add_imports(input["imports"], input["name"])
        return {"content": [{"type": "text", "text": result}]}

    @tool(
        name="compile_check",
        description=(
            "Check if lemma_helper_<name>.lean compiles. "
            "Returns 'OK: compiles (has sorry)' or 'OK: compiles (sorry-free)' or error details. "
            "Use after move_lines/add_imports to verify before final commit."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Helper name to check"},
            },
            "required": ["name"],
        },
    )
    async def compile_check_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.compile_check(input["name"])
        return {"content": [{"type": "text", "text": result}]}

    @tool(
        name="revert_last",
        description="Undo the last move_lines: restores Stub.lean to its state before that move and deletes the extracted file. Can be called multiple times to undo several moves in reverse order.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def revert_last_tool(input: dict[str, Any]) -> dict[str, Any]:
        result = session.revert_last()
        return {"content": [{"type": "text", "text": result}]}

    return create_sdk_mcp_server(
        name="extractor_tools",
        version="1.0.0",
        tools=[get_declarations_tool, move_decl_tool, move_lines_tool,
               add_imports_tool, compile_check_tool, revert_last_tool, commit_tool, revert_tool],
    )


def create_writer_import_server(target_file: str, ancestor_modules: list[str], ledger=None, current_entry_id: str = ""):
    """Create an MCP server with import + prune tools for proof_writer.

    Tools:
    - add_import_safely: add an import with safety checks
    - prune_helper: prune a failed child helper (removes import, moves file to pruned/)
    """
    from .modules.po_lean import get_lean_tools

    @tool(
        name="add_import_safely",
        description=(
            "Safely add an import to your file. Checks that the import is not circular "
            "(doesn't import an ancestor in the proof DAG), verifies the module exists, "
            "and confirms the file still compiles after adding. "
            "Use this instead of manually editing imports. "
            "Pass either a full module path (e.g. 'StrataAgent.Sandbox.decomposed.lemma_helper_foo') "
            "or search the ledger first and pass the module path from there."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "module_path": {
                    "type": "string",
                    "description": "Full module path to import (e.g. 'StrataAgent.Sandbox.decomposed.lemma_helper_sim_stmt_terminal')",
                },
            },
            "required": ["module_path"],
        },
    )
    async def add_import_safely_tool(input: dict[str, Any]) -> dict[str, Any]:
        tools = get_lean_tools()
        module_path = input["module_path"]
        import_line = f"import {module_path}"

        # Check circularity: is this an ancestor's Stub?
        circular_modules = {f"{anc}.Stub" for anc in ancestor_modules}
        if module_path in circular_modules:
            return {"content": [{"type": "text", "text":
                f"BLOCKED: '{module_path}' is an ancestor's Stub in the proof DAG. "
                f"Importing it would create a circular dependency. "
                f"You must prove this without importing ancestors."}]}

        # Check if already imported
        root = tools._root
        source = root / target_file
        if not source.exists():
            return {"content": [{"type": "text", "text": f"Error: {target_file} does not exist"}]}

        content = source.read_text()
        lines = content.splitlines()
        if import_line in [l.strip() for l in lines]:
            return {"content": [{"type": "text", "text": f"OK: already imported ({module_path})"}]}

        # Add the import after the last existing import
        insert_pos = 0
        for i, l in enumerate(lines):
            if l.strip().startswith("import "):
                insert_pos = i + 1
        lines.insert(insert_pos, import_line)
        source.write_text("\n".join(lines))

        # Verify it compiles
        cr = tools.check_compiles(target_file)
        if not cr.success:
            # Revert
            source.write_text(content)
            return {"content": [{"type": "text", "text":
                f"FAILED: Adding '{import_line}' breaks compilation. Reverted. "
                f"The module may not exist or has errors."}]}

        return {"content": [{"type": "text", "text":
            f"OK: added '{import_line}' — file compiles."}]}

    @tool(
        name="prune_helper",
        description=(
            "Prune a failed helper lemma from your decomposition. "
            "This removes the import from your Stub.lean, moves the helper file to a pruned/ folder, "
            "and marks it as PRUNED in the ledger. Use this when a helper you created turned out to be "
            "unprovable and you want to restructure your proof without it. "
            "You can only prune YOUR OWN children (helpers you decomposed)."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "name": {
                    "type": "string",
                    "description": "Name of the helper to prune (as it appears in the ledger)",
                },
            },
            "required": ["name"],
        },
    )
    async def prune_helper_tool(input: dict[str, Any]) -> dict[str, Any]:
        import shutil
        from .modules.lemma_ledger import LemmaStatus

        if not ledger or not current_entry_id:
            return {"content": [{"type": "text", "text": "Error: ledger not available for pruning"}]}

        helper_name = input["name"]
        tools = get_lean_tools()
        root = tools._root

        # Find the helper in the ledger
        target_entry = ledger.find_by_name(helper_name) if hasattr(ledger, 'find_by_name') else None
        if not target_entry:
            # Fallback: search by name
            for e in ledger.entries():
                if e.name == helper_name:
                    target_entry = e
                    break
        if not target_entry:
            return {"content": [{"type": "text", "text": f"Error: '{helper_name}' not found in ledger"}]}

        # Security: can only prune own children
        if target_entry.parent_id != current_entry_id:
            return {"content": [{"type": "text", "text":
                f"Error: '{helper_name}' is not your child (parent={target_entry.parent_id[:8]}). "
                f"You can only prune helpers you decomposed."}]}

        # Cannot prune PROVED entries
        if target_entry.status == LemmaStatus.PROVED:
            return {"content": [{"type": "text", "text":
                f"Error: '{helper_name}' is PROVED — cannot prune proved lemmas."}]}

        # Remove import from Stub.lean
        source = root / target_file
        if source.exists():
            content = source.read_text()
            module_path = target_entry.file_path.replace("/", ".").removesuffix(".lean")
            import_line = f"import {module_path}"
            lines = content.splitlines()
            lines = [l for l in lines if l.strip() != import_line]
            source.write_text("\n".join(lines))

        # Move file to pruned/ folder
        helper_file = root / target_entry.file_path
        if helper_file.exists():
            workspace_dir = helper_file.parent
            pruned_dir = workspace_dir.parent / "pruned"
            pruned_dir.mkdir(parents=True, exist_ok=True)
            dest = pruned_dir / helper_file.name
            shutil.move(str(helper_file), str(dest))

        # Mark as PRUNED in ledger (cascades to children)
        ledger.prune_branch(target_entry.id, f"Pruned by writer: approach abandoned")

        return {"content": [{"type": "text", "text":
            f"OK: pruned '{helper_name}' — import removed, file moved to pruned/, "
            f"entry marked PRUNED in ledger."}]}

    return create_sdk_mcp_server(
        name="writer_imports",
        version="1.0.0",
        tools=[add_import_safely_tool, prune_helper_tool],
    )
