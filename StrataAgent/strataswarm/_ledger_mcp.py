"""MCP server exposing the Lemma Ledger as read-only tools.

Agents (proof_guide, proof_writer, cycle_detector) query the ledger to find
similar lemmas, check what's proved, and understand the DAG structure.
All mutation is done mechanically by the orchestrator — agents cannot modify the DAG.
"""

from __future__ import annotations

import json
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool


def create_ledger_mcp_server(ledger: "LemmaLedger"):
    """Create a read-only MCP server for lemma ledger queries.

    Tools:
      - ledger_search: BM25 search over lemma statements (paginated)
      - ledger_get: get full details of a lemma by ID
      - ledger_dag: get the DAG structure as mermaid
      - ledger_children: get children of a node
      - ledger_ancestry: get ancestry chain of a node
      - ledger_stats: summary statistics
    """
    from .modules.lemma_ledger import LemmaLedger, LemmaStatus

    @tool(
        name="ledger_search",
        description=(
            "Search the lemma ledger using a free-text query. "
            "Searches over theorem names, signatures, parameter types, and return types. "
            "Returns ranked results with ID, name, status, statement, and file path. "
            "Use this to find similar lemmas that might already be proved or pending."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "query": {
                    "type": "string",
                    "description": "Search query (e.g. 'StepKleeneStar terminal Stmt', 'CanFail sim', 'eval preserved')",
                },
                "page": {
                    "type": "integer",
                    "description": "Page number (0-indexed). Use for pagination through results.",
                    "default": 0,
                },
                "page_size": {
                    "type": "integer",
                    "description": "Results per page.",
                    "default": 10,
                },
                "status_filter": {
                    "type": "array",
                    "items": {"type": "string", "enum": ["pending", "proving", "proved", "failed", "cycle", "pruned"]},
                    "description": "Only return entries with these statuses. Omit for all.",
                },
            },
            "required": ["query"],
        },
    )
    async def ledger_search(input: dict[str, Any]) -> dict[str, Any]:
        query = input["query"]
        page = input.get("page", 0)
        page_size = input.get("page_size", 10)
        status_filter = None
        if "status_filter" in input and input["status_filter"]:
            status_filter = [LemmaStatus(s) for s in input["status_filter"]]

        result = ledger.search(query, page=page, page_size=page_size, status_filter=status_filter)

        hits = []
        for hit in result.hits:
            e = hit.entry
            hits.append({
                "id": e.id,
                "name": e.name,
                "status": e.status.value,
                "score": round(hit.score, 3),
                "statement": e.statement,
                "file_path": e.file_path,
                "depth": e.depth,
                "is_mutual": e.is_mutual,
                "indegree": ledger.indegree(e.id),
            })

        return {"content": [{"type": "text", "text": json.dumps({
            "hits": hits,
            "total": result.total,
            "page": result.page,
            "page_size": result.page_size,
            "has_next": result.has_next,
            "total_pages": result.total_pages,
        }, indent=2)}]}

    @tool(
        name="ledger_get",
        description=(
            "Get full details of a lemma by its ID. "
            "Returns name, status, statement, file path, parent, children, depth, indegree, "
            "and other metadata."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "id": {
                    "type": "string",
                    "description": "The lemma entry ID (e.g. 'a1b2c3d4e5f6')",
                },
            },
            "required": ["id"],
        },
    )
    async def ledger_get(input: dict[str, Any]) -> dict[str, Any]:
        entry = ledger.get(input["id"])
        if not entry:
            return {"content": [{"type": "text", "text": json.dumps({"error": f"Entry {input['id']} not found"})}]}

        return {"content": [{"type": "text", "text": json.dumps({
            "id": entry.id,
            "name": entry.name,
            "status": entry.status.value,
            "statement": entry.statement,
            "file_path": entry.file_path,
            "workspace": entry.workspace,
            "parent_id": entry.parent_id,
            "children": entry.children,
            "depth": entry.depth,
            "indegree": ledger.indegree(entry.id),
            "attempts": entry.attempts,
            "turn_budget": entry.turn_budget,
            "is_mutual": entry.is_mutual,
            "import_path": entry.import_path,
            "proved_by": entry.proved_by,
            "failure_reason": entry.failure_reason,
            "pruned_reason": entry.pruned_reason,
            "cycle_ancestor_id": entry.cycle_ancestor_id,
        }, indent=2)}]}

    @tool(
        name="ledger_children",
        description="Get all children of a lemma (the sub-lemmas it was decomposed into).",
        input_schema={
            "type": "object",
            "properties": {
                "id": {"type": "string", "description": "Parent lemma ID"},
            },
            "required": ["id"],
        },
    )
    async def ledger_children(input: dict[str, Any]) -> dict[str, Any]:
        children = ledger.get_children(input["id"])
        result = [{
            "id": c.id,
            "name": c.name,
            "status": c.status.value,
            "statement": c.statement,
            "file_path": c.file_path,
            "indegree": ledger.indegree(c.id),
        } for c in children]
        return {"content": [{"type": "text", "text": json.dumps(result, indent=2)}]}

    @tool(
        name="ledger_ancestry",
        description=(
            "Get the ancestry chain of a lemma (parent → grandparent → ... → root). "
            "Useful for understanding the decomposition path that led to this lemma."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "id": {"type": "string", "description": "Lemma ID to trace ancestry for"},
            },
            "required": ["id"],
        },
    )
    async def ledger_ancestry(input: dict[str, Any]) -> dict[str, Any]:
        ancestry_ids = ledger.get_ancestry(input["id"])
        result = []
        for aid in ancestry_ids:
            entry = ledger.get(aid)
            if entry:
                result.append({
                    "id": entry.id,
                    "name": entry.name,
                    "status": entry.status.value,
                    "depth": entry.depth,
                })
        return {"content": [{"type": "text", "text": json.dumps(result, indent=2)}]}

    @tool(
        name="ledger_dag",
        description="Get the full lemma DAG as a Mermaid flowchart diagram.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def ledger_dag(input: dict[str, Any]) -> dict[str, Any]:
        mermaid = ledger.render_mermaid()
        return {"content": [{"type": "text", "text": mermaid}]}

    @tool(
        name="ledger_stats",
        description="Get summary statistics of the lemma ledger (counts by status, root info).",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def ledger_stats(input: dict[str, Any]) -> dict[str, Any]:
        entries = ledger.entries()
        stats = {
            "total": len(entries),
            "proved": sum(1 for e in entries if e.status == LemmaStatus.PROVED),
            "pending": sum(1 for e in entries if e.status == LemmaStatus.PENDING),
            "proving": sum(1 for e in entries if e.status == LemmaStatus.PROVING),
            "failed": sum(1 for e in entries if e.status == LemmaStatus.FAILED),
            "cycle": sum(1 for e in entries if e.status == LemmaStatus.CYCLE),
            "pruned": sum(1 for e in entries if e.status == LemmaStatus.PRUNED),
            "root_id": ledger.root_id,
        }
        root = ledger.get(ledger.root_id)
        if root:
            stats["root_name"] = root.name
            stats["root_status"] = root.status.value
        return {"content": [{"type": "text", "text": json.dumps(stats, indent=2)}]}

    return create_sdk_mcp_server(
        name="ledger",
        version="1.0.0",
        tools=[ledger_search, ledger_get, ledger_children, ledger_ancestry,
               ledger_dag, ledger_stats],
    )
