"""Destructive MCP server exposing the Lemma Ledger to the BigSur repair agent.

This is the WRITE-capable counterpart of `_ledger_mcp.create_ledger_mcp_server`
(which is read-only and given to guides/writers). Only BigSur — the repair agent
spawned on a give-up — gets this server, so only BigSur can physically delete
entries, rewrite signatures, or reparent nodes in the DAG.

It binds to the SAME live `LemmaLedger` instance the orchestrator holds, so
BigSur's mutations are reflected in memory immediately; the orchestrator's normal
post-phase `ledger.save()` then persists them. No disk/JSON round-trip, no reload.

Tools (destructive, on top of the read tools):
  - ledger_search / ledger_get / ledger_children / ledger_ancestry / ledger_dag /
    ledger_stats  (same as the read-only server)
  - ledger_delete_entry        : hard-delete one entry (unlink from parents)
  - ledger_purge_subtree       : hard-delete an entry + all its descendants
  - ledger_update_signature    : rewrite a statement, recompute hash, reset PENDING
  - ledger_reparent            : move a node under a new parent (cycle-guarded)
  - ledger_reset_to_pending    : clear failure/cycle, mark PENDING for re-proof
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, Any

from claude_agent_sdk import create_sdk_mcp_server, tool

if TYPE_CHECKING:
    from .modules.lemma_ledger import LemmaLedger


def create_bigsur_ledger_mcp_server(ledger: "LemmaLedger"):
    """Create a WRITE-capable ledger MCP server for the BigSur repair agent.

    Binds to the live ledger instance so mutations are immediately visible to the
    orchestrator. NEVER attach this to guides/writers — they get the read-only
    server from `_ledger_mcp.create_ledger_mcp_server`.
    """
    from .modules.lemma_ledger import LemmaStatus

    def _text(payload: Any) -> dict[str, Any]:
        return {"content": [{"type": "text",
                             "text": json.dumps(payload, indent=2) if not isinstance(payload, str) else payload}]}

    # ── Read tools (mirror the read-only server so BigSur has one server) ──────

    @tool(
        name="ledger_search",
        description=(
            "Search the lemma ledger by free text over names/signatures/types. "
            "Returns ranked hits with id, name, status, statement, file_path."),
        input_schema={
            "type": "object",
            "properties": {
                "query": {"type": "string"},
                "page": {"type": "integer", "default": 0},
                "page_size": {"type": "integer", "default": 10},
                "status_filter": {
                    "type": "array",
                    "items": {"type": "string",
                              "enum": ["pending", "proving", "proved", "failed", "cycle", "pruned"]},
                },
            },
            "required": ["query"],
        },
    )
    async def ledger_search(input: dict[str, Any]) -> dict[str, Any]:
        status_filter = None
        if input.get("status_filter"):
            status_filter = [LemmaStatus(s) for s in input["status_filter"]]
        result = ledger.search(input["query"], page=input.get("page", 0),
                               page_size=input.get("page_size", 10),
                               status_filter=status_filter)
        hits = [{
            "id": h.entry.id, "name": h.entry.name, "status": h.entry.status.value,
            "score": round(h.score, 3), "statement": h.entry.statement,
            "file_path": h.entry.file_path, "depth": h.entry.depth,
            "indegree": ledger.indegree(h.entry.id),
        } for h in result.hits]
        return _text({"hits": hits, "total": result.total, "page": result.page,
                      "has_next": result.has_next, "total_pages": result.total_pages})

    @tool(
        name="ledger_get",
        description="Full details of one lemma by ID (statement, file_path, parent, children, status).",
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_get(input: dict[str, Any]) -> dict[str, Any]:
        e = ledger.get(input["id"])
        if not e:
            return _text({"error": f"Entry {input['id']} not found"})
        return _text({
            "id": e.id, "name": e.name, "status": e.status.value, "statement": e.statement,
            "file_path": e.file_path, "workspace": e.workspace, "parent_id": e.parent_id,
            "children": e.children, "depth": e.depth, "indegree": ledger.indegree(e.id),
            "import_path": e.import_path, "proved_by": e.proved_by,
            "failure_reason": e.failure_reason, "signature_hash": e.signature_hash,
        })

    @tool(
        name="ledger_children",
        description="Direct children (sub-lemmas) of a node.",
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_children(input: dict[str, Any]) -> dict[str, Any]:
        return _text([{
            "id": c.id, "name": c.name, "status": c.status.value,
            "statement": c.statement, "file_path": c.file_path,
        } for c in ledger.get_children(input["id"])])

    @tool(
        name="ledger_ancestry",
        description="Ancestry chain parent → grandparent → ... → root for a node.",
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_ancestry(input: dict[str, Any]) -> dict[str, Any]:
        out = []
        for aid in ledger.get_ancestry(input["id"]):
            e = ledger.get(aid)
            if e:
                out.append({"id": e.id, "name": e.name, "status": e.status.value,
                            "file_path": e.file_path, "statement": e.statement})
        return _text(out)

    @tool(
        name="ledger_dag",
        description="The full lemma DAG as a Mermaid flowchart.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def ledger_dag(input: dict[str, Any]) -> dict[str, Any]:
        return _text(ledger.render_mermaid())

    @tool(
        name="ledger_stats",
        description="Summary counts by status + root info.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def ledger_stats(input: dict[str, Any]) -> dict[str, Any]:
        entries = ledger.entries()
        stats = {s.value: sum(1 for e in entries if e.status == s) for s in LemmaStatus}
        stats["total"] = len(entries)
        stats["root_id"] = ledger.root_id
        root = ledger.get(ledger.root_id)
        if root:
            stats["root_name"] = root.name
            stats["root_status"] = root.status.value
        return _text(stats)

    # ── Destructive tools (BigSur only) ────────────────────────────────────────

    @tool(
        name="ledger_delete_entry",
        description=(
            "HARD-DELETE a single ledger entry and unlink it from all parents. Its "
            "children are left orphaned — prefer ledger_purge_subtree if you mean the "
            "whole subtree. Use when a decomposition node no longer corresponds to any "
            "file/decl after your fix. Cannot delete the root."),
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_delete_entry(input: dict[str, Any]) -> dict[str, Any]:
        return _text(ledger.bigsur_delete_entry(input["id"]))

    @tool(
        name="ledger_purge_subtree",
        description=(
            "HARD-DELETE an entry AND all its descendants (the whole decomposition "
            "subtree). Nodes still referenced by a live branch outside the subtree are "
            "kept. Returns the list of deleted IDs. Use when you removed a bad "
            "decomposition's files and the ledger subtree must go with them."),
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_purge_subtree(input: dict[str, Any]) -> dict[str, Any]:
        deleted = ledger.bigsur_purge_subtree(input["id"])
        return _text({"deleted": deleted, "count": len(deleted)})

    @tool(
        name="ledger_update_signature",
        description=(
            "Rewrite an entry's statement/signature to match a strengthened contract. "
            "Recomputes the signature hash and RESETS the entry to PENDING (a changed "
            "contract invalidates any prior proof and must be re-proved). Pass the FULL "
            "new theorem statement line(s), e.g. 'theorem foo (h : P) : Q := by sorry'."),
        input_schema={
            "type": "object",
            "properties": {"id": {"type": "string"}, "new_statement": {"type": "string"}},
            "required": ["id", "new_statement"],
        },
    )
    async def ledger_update_signature(input: dict[str, Any]) -> dict[str, Any]:
        return _text(ledger.bigsur_update_signature(input["id"], input["new_statement"]))

    @tool(
        name="ledger_reparent",
        description=(
            "Move a node under a new parent (cycle-guarded — refuses if it would form a "
            "cycle). Use when the correct supplier of a fact is a different ancestor than "
            "the one it was decomposed under."),
        input_schema={
            "type": "object",
            "properties": {"child_id": {"type": "string"}, "new_parent_id": {"type": "string"}},
            "required": ["child_id", "new_parent_id"],
        },
    )
    async def ledger_reparent(input: dict[str, Any]) -> dict[str, Any]:
        return _text(ledger.bigsur_reparent(input["child_id"], input["new_parent_id"]))

    @tool(
        name="ledger_reset_to_pending",
        description=(
            "Clear an entry's failure/cycle state and mark it PENDING (priority-boosted) "
            "so it is re-proved — WITHOUT changing its signature. Use for a lemma whose "
            "contract you fixed elsewhere (e.g. a parent now supplies the missing "
            "hypothesis) so it should be re-attempted against the corrected environment."),
        input_schema={"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"]},
    )
    async def ledger_reset_to_pending(input: dict[str, Any]) -> dict[str, Any]:
        return _text(ledger.bigsur_reset_to_pending(input["id"]))

    return create_sdk_mcp_server(
        name="bigsur_ledger",
        version="1.0.0",
        tools=[ledger_search, ledger_get, ledger_children, ledger_ancestry,
               ledger_dag, ledger_stats,
               ledger_delete_entry, ledger_purge_subtree, ledger_update_signature,
               ledger_reparent, ledger_reset_to_pending],
    )
