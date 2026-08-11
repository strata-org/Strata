"""Lemma Ledger: Global worklist for proof obligations.

Tracks all lemmas (pending, proved, failed, cyclic, pruned) across the entire
proof session. Lightweight — entries store file pointers, not content.
Signature extraction is handled externally via Lean tools (split_theorems, etc.).

Provides priority ordering, cycle detection, DAG visualization, BM25 search,
and persistence. Pure Python — no agent/swarm dependencies.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import secrets
import threading
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Any


class LemmaStatus(str, Enum):
    PENDING = "pending"
    PROVING = "proving"
    CONTINGENT = "contingent"  # decomposed — proof depends on children being proved
    PROVED = "proved"
    FAILED = "failed"
    CYCLE = "cycle"
    PRUNED = "pruned"


def _new_id() -> str:
    return secrets.token_hex(6)


@dataclass
class LemmaEntry:
    """Lightweight entry — points to a file, stores statement for search indexing."""
    id: str
    name: str                    # theorem name (for display/search)
    file_path: str               # pointer to .lean file (one theorem or mutual group)
    workspace: str               # workspace dir for this lemma
    signature_hash: str          # precomputed hash for fast cycle detection
    statement: str = ""          # "theorem <name> <params> : <type> := by sorry" (for BM25 index, no proof body)
    status: LemmaStatus = LemmaStatus.PENDING
    parent_id: str = ""
    children: list[str] = field(default_factory=list)  # IDs of children (= dependents)
    depth: int = 0
    attempts: int = 0
    max_attempts: int = 3
    turn_budget: int = 25
    priority_boost: bool = False   # set when re-activated after cycle/fail — must be proved first
    guide_name: str = ""
    writer_name: str = ""
    import_path: str = ""        # lean import path (set when proved)
    proved_by: str = ""          # "direct" | "shortcut" | "assembly"
    failure_reason: str = ""
    siblings_at_failure: list[str] = field(default_factory=list)  # names of siblings in same decomposition when this failed
    pruned_reason: str = ""
    cycle_ancestor_id: str = ""
    is_mutual: bool = False      # True if file contains a mutual block


# ─── Search infrastructure ───────────────────────────────────────────────────

def _tokenize(text: str) -> list[str]:
    """Tokenize on camelCase splits, underscores, whitespace."""
    camel_split = re.sub(r'([a-z])([A-Z])', r'\1 \2', text)
    camel_split = re.sub(r'([A-Z]+)([A-Z][a-z])', r'\1 \2', camel_split)
    tokens = re.findall(r'[a-zA-Z][a-zA-Z0-9]*', camel_split)
    return [t.lower() for t in tokens]


def _bm25_score(
    query_terms: list[str],
    doc_terms: list[str],
    avg_dl: float,
    n_docs: int,
    doc_freq: dict[str, int],
    k1: float = 1.5,
    b: float = 0.75,
) -> float:
    """BM25 score for a single document against a query."""
    dl = len(doc_terms)
    if dl == 0:
        return 0.0

    doc_tf: dict[str, int] = {}
    for t in doc_terms:
        doc_tf[t] = doc_tf.get(t, 0) + 1

    score = 0.0
    for term in set(query_terms):
        tf = doc_tf.get(term, 0)
        if tf == 0:
            continue
        df = doc_freq.get(term, 0)
        idf = math.log((n_docs - df + 0.5) / (df + 0.5) + 1.0)
        tf_norm = (tf * (k1 + 1)) / (tf + k1 * (1 - b + b * dl / max(avg_dl, 1)))
        score += idf * tf_norm

    return score


@dataclass
class SearchHit:
    entry: LemmaEntry
    score: float


@dataclass
class SearchResult:
    hits: list[SearchHit]
    total: int
    page: int
    page_size: int

    @property
    def has_next(self) -> bool:
        return (self.page + 1) * self.page_size < self.total

    @property
    def total_pages(self) -> int:
        return (self.total + self.page_size - 1) // self.page_size


# ─── Ledger ──────────────────────────────────────────────────────────────────

class LemmaLedger:
    """Programmatic ledger for lemma tracking, cycle detection, and priority."""

    def __init__(self, path: Path):
        self._path = path
        self._lock = threading.Lock()
        self._entries: dict[str, LemmaEntry] = {}  # keyed by id
        self._root_id: str = ""
        self._indegree: dict[str, int] = {}  # entry_id → number of parents pointing to it
        if path.exists():
            self._load()
            self._rebuild_indegree()

    def _rebuild_indegree(self):
        """Recompute indegree cache from children lists."""
        self._indegree = {}
        for entry in self._entries.values():
            for child_id in entry.children:
                self._indegree[child_id] = self._indegree.get(child_id, 0) + 1

    def indegree(self, entry_id: str) -> int:
        """How many entries list this ID as a child (= how many things depend on it)."""
        with self._lock:
            return self._indegree.get(entry_id, 0)

    # ─── Registration ────────────────────────────────────────────────────────

    def add_lemma(
        self, name: str, file_path: str, workspace: str,
        signature_hash: str, statement: str = "", is_mutual: bool = False,
        parent_id: str = "",
    ) -> LemmaEntry | str:
        """Create and register a lemma.

        If parent_id is provided, the lemma is added as a child of that parent
        (with cycle detection). If parent_id is empty, this is a root lemma.

        Args:
            statement: The theorem statement for BM25 indexing.
                       Format: "theorem <name> <params> : <type> := by sorry"
                       (no proof body — just the declaration stub)

        Returns the LemmaEntry on success, or an error string if cycle detected.
        """
        with self._lock:
            depth = 0
            if parent_id:
                parent = self._entries.get(parent_id)
                if not parent:
                    return f"Parent {parent_id} not found"

                # Cycle check: walk up from parent
                if parent.signature_hash == signature_hash:
                    return "Cycle: signature matches direct parent"
                if self._check_cycle_unlocked(signature_hash, parent_id):
                    return "Cycle: signature matches ancestor in chain"

                depth = parent.depth + 1

            entry = LemmaEntry(
                id=_new_id(),
                name=name,
                file_path=file_path,
                workspace=workspace,
                signature_hash=signature_hash,
                statement=statement,
                parent_id=parent_id,
                depth=depth,
                status=LemmaStatus.PENDING,
                is_mutual=is_mutual,
            )
            self._entries[entry.id] = entry

            if not parent_id:
                self._root_id = entry.id
            else:
                parent = self._entries[parent_id]
                parent.children.append(entry.id)
                self._indegree[entry.id] = self._indegree.get(entry.id, 0) + 1

            return entry

    def add_parent(self, parent_id: str, child_id: str) -> str | None:
        """Add an edge from parent to child (cross-branch sharing).

        Returns error string if this would create a cycle, None on success.
        """
        with self._lock:
            parent = self._entries.get(parent_id)
            child = self._entries.get(child_id)
            if not parent or not child:
                return "Parent or child not found"
            if child_id in parent.children:
                return None  # already connected

            # Check: would adding this edge create a cycle?
            # A cycle exists if parent is a descendant of child (child → ... → parent path exists)
            if self._is_descendant_of(parent_id, child_id):
                return "Cycle: parent is a descendant of child"

            parent.children.append(child_id)
            self._indegree[child_id] = self._indegree.get(child_id, 0) + 1
            return None

    def _is_descendant_of(self, node_id: str, ancestor_id: str) -> bool:
        """True if node_id is reachable by walking down from ancestor_id's children."""
        visited = set()
        queue = [ancestor_id]
        while queue:
            current = queue.pop()
            if current == node_id:
                return True
            if current in visited:
                continue
            visited.add(current)
            entry = self._entries.get(current)
            if entry:
                queue.extend(entry.children)
        return False

    # ─── Queries ─────────────────────────────────────────────────────────────

    def get(self, entry_id: str) -> LemmaEntry | None:
        with self._lock:
            return self._entries.get(entry_id)

    @property
    def root_id(self) -> str:
        return self._root_id

    def pick_next(self) -> LemmaEntry | None:
        """Mechanical fallback for selecting next PENDING lemma.

        Used only when the strategist agent is unavailable. Prefers:
        1. Boosted entries (re-activated after cycle/fail)
        2. Deeper nodes with higher indegree (DFS bias)
        """
        with self._lock:
            pending = [e for e in self._entries.values()
                       if e.status == LemmaStatus.PENDING]
            if not pending:
                return None

            boosted = [e for e in pending if e.priority_boost]
            if boosted:
                boosted.sort(key=lambda e: (self._indegree.get(e.id, 0), e.depth), reverse=True)
                winner = boosted[0]
                winner.turn_budget = 25 + self._indegree.get(winner.id, 0) * 5
                return winner

            pending.sort(key=lambda e: (e.depth, self._indegree.get(e.id, 0), -e.attempts), reverse=True)
            winner = pending[0]
            winner.turn_budget = 25 + self._indegree.get(winner.id, 0) * 5
            return winner

    def pick_boosted(self) -> LemmaEntry | None:
        """Return the highest-priority boosted PENDING entry, or None.

        A `priority_boost` on a PENDING entry is a deliberate NOMINATION — almost
        always BigSur having just re-opened THE node that must be proved next
        (bigsur_update_signature / bigsur_reset_to_pending both set the boost).
        SELECT honors it directly instead of re-asking the guide (which lacks
        BigSur's just-computed repair context and re-litigates into root/sibling
        churn — the callElim loop). Does NOT clear the boost or change status —
        the caller does that via mark_proving so the nomination fires exactly once.
        Ranking mirrors pick_next's boosted branch (indegree, then depth)."""
        with self._lock:
            boosted = [e for e in self._entries.values()
                       if e.status == LemmaStatus.PENDING and e.priority_boost]
            if not boosted:
                return None
            boosted.sort(key=lambda e: (self._indegree.get(e.id, 0), e.depth), reverse=True)
            return boosted[0]

    def pending_children(self, entry_id: str) -> list[LemmaEntry]:
        """Return PENDING children of an entry (for strategist to examine)."""
        with self._lock:
            parent = self._entries.get(entry_id)
            if not parent:
                return []
            return [self._entries[cid] for cid in parent.children
                    if cid in self._entries
                    and self._entries[cid].status == LemmaStatus.PENDING]

    def has_pending(self) -> bool:
        """True if any entry is PENDING."""
        with self._lock:
            return any(e.status == LemmaStatus.PENDING for e in self._entries.values())

    # ─── Search (BM25) ───────────────────────────────────────────────────────

    def search(self, query: str, page: int = 0, page_size: int = 10,
               status_filter: list[LemmaStatus] | None = None) -> SearchResult:
        """BM25-ranked search over lemma statements (name, params, type).

        The index is built from each entry's `statement` field which contains
        the full theorem declaration stub (everything except the proof body):
            "theorem <name> <params> : <type> := by sorry"

        This allows searching by name, type components, parameter types, etc.
        """
        query_terms = _tokenize(query)
        if not query_terms:
            return SearchResult(hits=[], total=0, page=page, page_size=page_size)

        with self._lock:
            candidates = list(self._entries.values())
            if status_filter:
                candidates = [e for e in candidates if e.status in status_filter]

            doc_terms_cache = {e.id: _tokenize(e.statement or e.name) for e in candidates}
            avg_dl = sum(len(t) for t in doc_terms_cache.values()) / max(len(candidates), 1)

            df: dict[str, int] = {}
            for term in set(query_terms):
                count = sum(1 for terms in doc_terms_cache.values() if term in terms)
                df[term] = count

            scored: list[tuple[LemmaEntry, float]] = []
            for entry in candidates:
                score = _bm25_score(query_terms, doc_terms_cache[entry.id], avg_dl, len(candidates), df)
                if score > 0:
                    scored.append((entry, score))

            scored.sort(key=lambda x: x[1], reverse=True)
            total = len(scored)
            start = page * page_size
            end = start + page_size
            page_hits = scored[start:end]

            return SearchResult(
                hits=[SearchHit(entry=e, score=s) for e, s in page_hits],
                total=total,
                page=page,
                page_size=page_size,
            )

    # ─── Ancestry (computed on demand) ──────────────────────────────────────

    def get_ancestry(self, entry_id: str) -> list[str]:
        """Walk parent_id links to root. Returns list of ancestor IDs [parent, grandparent, ..., root]."""
        with self._lock:
            return self._get_ancestry_unlocked(entry_id)

    def _get_ancestry_unlocked(self, entry_id: str) -> list[str]:
        result = []
        current = self._entries.get(entry_id)
        while current and current.parent_id:
            result.append(current.parent_id)
            current = self._entries.get(current.parent_id)
        return result

    # ─── Cycle detection ─────────────────────────────────────────────────────

    def _check_cycle_unlocked(self, signature_hash: str, entry_id: str) -> bool:
        """Walk up parent chain from entry_id, check if any ancestor has matching sig hash."""
        for ancestor_id in self._get_ancestry_unlocked(entry_id):
            ancestor = self._entries.get(ancestor_id)
            if ancestor and ancestor.signature_hash == signature_hash:
                return True
        return False

    def check_cycle(self, signature_hash: str, entry_id: str) -> bool:
        """True if signature_hash matches any ancestor of entry_id.

        Walks parent_id links up to root — no stored ancestry needed.
        """
        with self._lock:
            return self._check_cycle_unlocked(signature_hash, entry_id)

    def get_cycle_ancestor(self, signature_hash: str, entry_id: str) -> LemmaEntry | None:
        """Find the ancestor whose signature_hash matches. Returns None if no cycle."""
        with self._lock:
            for ancestor_id in self._get_ancestry_unlocked(entry_id):
                ancestor = self._entries.get(ancestor_id)
                if ancestor and ancestor.signature_hash == signature_hash:
                    return ancestor
            return None

    # ─── Navigation ──────────────────────────────────────────────────────────

    def get_children(self, entry_id: str) -> list[LemmaEntry]:
        with self._lock:
            parent = self._entries.get(entry_id)
            if not parent:
                return []
            return [self._entries[cid] for cid in parent.children
                    if cid in self._entries]

    def get_parent(self, entry_id: str) -> LemmaEntry | None:
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry or not entry.parent_id:
                return None
            return self._entries.get(entry.parent_id)

    def get_all_parents(self, entry_id: str) -> list[LemmaEntry]:
        """Get ALL entries that have this entry in their children list (multi-parent)."""
        with self._lock:
            parents = []
            for e in self._entries.values():
                if entry_id in e.children:
                    parents.append(e)
            return parents

    def all_children_proved(self, entry_id: str) -> bool:
        children = self.get_children(entry_id)
        if not children:
            return False
        return all(c.status == LemmaStatus.PROVED for c in children)

    def root_is_proved(self) -> bool:
        with self._lock:
            root = self._entries.get(self._root_id)
            return root is not None and root.status == LemmaStatus.PROVED

    def root_is_blocked(self) -> bool:
        with self._lock:
            has_pending = any(e.status == LemmaStatus.PENDING for e in self._entries.values())
            has_proving = any(e.status == LemmaStatus.PROVING for e in self._entries.values())
            return not has_pending and not has_proving

    def all_proved(self) -> bool:
        with self._lock:
            for e in self._entries.values():
                if e.status in (LemmaStatus.PENDING, LemmaStatus.PROVING, LemmaStatus.CONTINGENT):
                    return False
            return True

    def entries(self) -> list[LemmaEntry]:
        with self._lock:
            return list(self._entries.values())

    # ─── Mutations ───────────────────────────────────────────────────────────

    def mark_proving(self, entry_id: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.PROVING
                entry.priority_boost = False

    def mark_contingent(self, entry_id: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.CONTINGENT
                entry.priority_boost = False

    def mark_pending(self, entry_id: str, priority_boost: bool = False):
        """Re-activate an entry to PENDING so SELECT re-picks it. Used to re-decompose
        a parent whose child gave up (priority_boost=True makes it jump the queue)."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.PENDING
                entry.priority_boost = priority_boost

    def mark_proved(self, entry_id: str, import_path: str, proved_by: str = "direct"):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.PROVED
                entry.import_path = import_path
                entry.proved_by = proved_by
                entry.priority_boost = False

    def mark_failed(self, entry_id: str, reason: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.FAILED
                entry.failure_reason = reason
                entry.priority_boost = False

    def mark_cycle(self, entry_id: str, ancestor_id: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.status = LemmaStatus.CYCLE
                entry.cycle_ancestor_id = ancestor_id
                entry.priority_boost = False

    def prune_branch(self, entry_id: str, reason: str) -> list[str]:
        """Mark entry + all descendants as pruned. Returns list of pruned IDs."""
        pruned = []
        with self._lock:
            self._prune_recursive(entry_id, reason, pruned)
        return pruned

    def _prune_recursive(self, entry_id: str, reason: str, acc: list[str]):
        entry = self._entries.get(entry_id)
        if not entry or entry.status in (LemmaStatus.PRUNED, LemmaStatus.PROVED, LemmaStatus.FAILED):
            return
        entry.status = LemmaStatus.PRUNED
        entry.pruned_reason = reason
        entry.priority_boost = False
        acc.append(entry_id)
        for child_id in entry.children:
            self._prune_recursive(child_id, f"ancestor '{entry.name}' pruned: {reason}", acc)

    def adjust_budget(self, entry_id: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.turn_budget = 25 + self._indegree.get(entry_id, 0) * 5

    def increment_attempts(self, entry_id: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.attempts += 1

    def set_agents(self, entry_id: str, writer_name: str, guide_name: str):
        with self._lock:
            entry = self._entries.get(entry_id)
            if entry:
                entry.writer_name = writer_name
                entry.guide_name = guide_name

    # ─── BigSur destructive mutators ───────────────────────────────────────────
    # HARD structural edits reserved for the BigSur repair agent, which only runs
    # on a give-up. Unlike prune_branch/mark_* (which just flip a status), these
    # physically remove entries and rewrite signatures — the DAG must be able to
    # match a post-fix reality where files/signatures were rewritten. Exposed ONLY
    # via create_bigsur_ledger_mcp_server; the normal (read-only) ledger MCP that
    # guides/writers see never sees them.

    def _unlink_from_parents(self, entry_id: str):
        """Remove entry_id from every parent's children list + fix indegree.
        Caller must hold the lock."""
        for e in self._entries.values():
            if entry_id in e.children:
                e.children = [c for c in e.children if c != entry_id]
        self._indegree.pop(entry_id, None)
        self._rebuild_indegree()

    def _repoint_orphaned_children(self, deleted_id: str):
        """After deleting `deleted_id`, fix any SURVIVING entry that still records
        it as `parent_id` (a stored back-pointer to a node that no longer exists —
        a ghost that would truncate get_ancestry). Re-point each such child to a
        parent that still lists it in `children` (a diamond may have one), else
        clear parent_id to "". Caller holds the lock and has already removed
        `deleted_id` from `self._entries` and from all parents' children lists."""
        for child in self._entries.values():
            if child.parent_id != deleted_id:
                continue
            surviving_parent = next(
                (p.id for p in self._entries.values() if child.id in p.children), "")
            child.parent_id = surviving_parent

    def bigsur_delete_entry(self, entry_id: str) -> str:
        """Hard-delete a SINGLE entry: remove it from the table and unlink it from
        all parents. Its children are re-parented to a surviving parent if one
        exists (a diamond may share them), otherwise orphaned (parent_id cleared) —
        never left pointing at the deleted node. Use bigsur_purge_subtree if you
        mean the whole subtree. Returns a status str."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry:
                return f"Entry {entry_id} not found"
            if entry_id == self._root_id:
                return "REFUSED: cannot delete the root entry"
            name = entry.name
            self._unlink_from_parents(entry_id)
            del self._entries[entry_id]
            self._repoint_orphaned_children(entry_id)
            return f"Deleted entry '{name}' ({entry_id})"

    def bigsur_purge_subtree(self, entry_id: str) -> list[str]:
        """Hard-delete an entry AND all its descendants. Returns deleted IDs.
        Refuses to purge the root.

        A descendant that is still reachable from a LIVE branch outside the purge is
        KEPT — and keeping it TRANSITIVELY protects its own descendants (a kept
        shared node is useless without the nodes holding it up). We compute the
        delete-set to a FIXPOINT: start with the whole subtree, then repeatedly
        rescue any node that has a parent not (yet) marked for deletion, until
        nothing changes. The explicitly-named purge root is always deleted (its
        parent is external by construction, but deleting it is the whole point)."""
        with self._lock:
            if entry_id == self._root_id:
                return []
            if entry_id not in self._entries:
                return []
            # Collect the subtree reachable from entry_id.
            subtree: set[str] = set()
            stack = [entry_id]
            while stack:
                cur = stack.pop()
                if cur in subtree:
                    continue
                e = self._entries.get(cur)
                if not e:
                    continue
                subtree.add(cur)
                stack.extend(e.children)

            # Fixpoint keep-set: a node is RESCUED (kept) if it has any parent NOT
            # in the current delete-set. Rescuing a node can rescue its children on
            # the next pass (their parent is no longer being deleted), so iterate
            # until stable. The named purge root is never rescued.
            to_delete = set(subtree) - {self._root_id}
            changed = True
            while changed:
                changed = False
                for eid in list(to_delete):
                    if eid == entry_id:
                        continue  # named purge root: always deleted
                    surviving_parents = [
                        p.id for p in self._entries.values()
                        if eid in p.children and p.id not in to_delete]
                    if surviving_parents:
                        to_delete.discard(eid)
                        changed = True

            deleted: list[str] = []
            for eid in list(to_delete):
                if eid not in self._entries:
                    continue
                self._unlink_from_parents(eid)
                del self._entries[eid]
                deleted.append(eid)
            # Fix any kept node that recorded a now-deleted node as its parent_id.
            for eid in deleted:
                self._repoint_orphaned_children(eid)
            return deleted

    def bigsur_update_signature(self, entry_id: str, new_statement: str) -> str:
        """Rewrite an entry's statement/signature. Recomputes signature_hash and
        RESETS the entry to PENDING (a changed contract invalidates any prior
        proof and must be re-proved). Clears failure/cycle state."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry:
                return f"Entry {entry_id} not found"
            entry.statement = new_statement
            entry.signature_hash = self.compute_signature_hash(new_statement)
            entry.status = LemmaStatus.PENDING
            entry.failure_reason = ""
            entry.cycle_ancestor_id = ""
            entry.pruned_reason = ""
            entry.priority_boost = True
            return (f"Updated signature of '{entry.name}' ({entry_id}); "
                    f"reset to PENDING for re-proof")

    def bigsur_reparent(self, child_id: str, new_parent_id: str) -> str:
        """Move child under a new parent (cycle-guarded). Detaches from all current
        parents first, then attaches to new_parent_id."""
        with self._lock:
            child = self._entries.get(child_id)
            parent = self._entries.get(new_parent_id)
            if not child or not parent:
                return "child or new parent not found"
            if child_id == new_parent_id:
                return "REFUSED: cannot parent an entry to itself"
            if self._is_descendant_of(new_parent_id, child_id):
                return "REFUSED: would create a cycle (new parent is under child)"
            self._unlink_from_parents(child_id)
            parent.children.append(child_id)
            child.parent_id = new_parent_id
            self._rebuild_indegree()
            return f"Reparented '{child.name}' under '{parent.name}'"

    def bigsur_reset_to_pending(self, entry_id: str) -> str:
        """Clear failure/cycle state and mark PENDING (priority-boosted) so SELECT
        re-picks it. For re-proving a lemma whose contract BigSur just fixed
        elsewhere, without changing its own signature."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry:
                return f"Entry {entry_id} not found"
            entry.status = LemmaStatus.PENDING
            entry.failure_reason = ""
            entry.cycle_ancestor_id = ""
            entry.pruned_reason = ""
            entry.priority_boost = True
            return f"Reset '{entry.name}' ({entry_id}) to PENDING"

    def bigsur_set_status(self, entry_id: str, status: str) -> str:
        """Set an entry's status to any NON-proved status
        (pending/proving/contingent/failed/pruned/cycle) and clear stale
        failure/cycle/pruned annotations. Free-form bookkeeping fix for a
        mis-marked entry. PROVED is refused here — it must go through
        bigsur_mark_proved, which verifies sorry-freedom via the oracle (marking
        something proved without verification is itself an inconsistency)."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry:
                return f"Entry {entry_id} not found"
            try:
                new_status = LemmaStatus(status)
            except ValueError:
                return (f"Invalid status '{status}'. Valid: pending, proving, "
                        f"contingent, failed, pruned, cycle (proved → use ledger_mark_proved).")
            if new_status == LemmaStatus.PROVED:
                return "REFUSED: use ledger_mark_proved (oracle-verified) to mark PROVED."
            prev = entry.status.value
            entry.status = new_status
            entry.failure_reason = ""
            entry.cycle_ancestor_id = ""
            entry.pruned_reason = ""
            return f"Set '{entry.name}' ({entry_id}) status {prev} → {new_status.value}"

    def bigsur_mark_proved(self, entry_id: str, import_path: str) -> str:
        """Correct a mis-marked ledger status: record a lemma as PROVED and clear any
        stale failure/pruned/cycle state. For the desync case where a lemma's FILE is
        already sorry-free but its ledger entry says failed/pruned — which otherwise
        loops (reset_to_pending → re-select → re-escalate). CALLER MUST have verified
        sorry-freedom first (the MCP tool gates this on the axioms oracle)."""
        with self._lock:
            entry = self._entries.get(entry_id)
            if not entry:
                return f"Entry {entry_id} not found"
            prev = entry.status.value
            entry.status = LemmaStatus.PROVED
            entry.import_path = import_path or entry.import_path
            entry.proved_by = "bigsur_verified"
            entry.failure_reason = ""
            entry.cycle_ancestor_id = ""
            entry.pruned_reason = ""
            entry.priority_boost = False
            return f"Marked '{entry.name}' ({entry_id}) PROVED (was {prev})"

    # ─── Persistence ─────────────────────────────────────────────────────────

    def save(self):
        """Atomic write to disk + regenerate DAG visualizations (tree + mermaid)."""
        with self._lock:
            data = {
                "version": 1,
                "root_id": self._root_id,
                "entries": {eid: asdict(e) for eid, e in self._entries.items()},
            }
        self._path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self._path.with_suffix(".tmp")
        tmp.write_text(json.dumps(data, indent=2))
        tmp.replace(self._path)

        dag_dir = self._path.parent
        dag_dir.joinpath("lemma_dag.md").write_text(self.render_dag())
        dag_dir.joinpath("lemma_dag_mermaid.md").write_text(self.render_mermaid())

    def _load(self):
        try:
            data = json.loads(self._path.read_text())
        except (json.JSONDecodeError, OSError):
            return

        self._root_id = data.get("root_id", "")
        raw_entries = data.get("entries", {})
        for eid, raw in raw_entries.items():
            raw["status"] = LemmaStatus(raw["status"])
            self._entries[eid] = LemmaEntry(**{
                k: v for k, v in raw.items()
                if k in LemmaEntry.__dataclass_fields__
            })

    # ─── DAG Visualization ───────────────────────────────────────────────────

    def render_dag(self) -> str:
        """Render the proof DAG as indented markdown tree."""
        with self._lock:
            if not self._root_id:
                return "# Lemma DAG\n\n(empty)\n"

            lines = ["# Lemma DAG\n"]
            self._render_node(self._root_id, 0, lines, set())

            total = len(self._entries)
            proved = sum(1 for e in self._entries.values() if e.status == LemmaStatus.PROVED)
            cycles = sum(1 for e in self._entries.values() if e.status == LemmaStatus.CYCLE)
            pruned = sum(1 for e in self._entries.values() if e.status == LemmaStatus.PRUNED)
            failed = sum(1 for e in self._entries.values() if e.status == LemmaStatus.FAILED)
            pending = sum(1 for e in self._entries.values() if e.status == LemmaStatus.PENDING)

            lines.append("")
            lines.append("Legend: ✅ proved | ⟳ cycle | ✗ pruned | ✗✗ failed | ⏳ pending | 🔨 proving")
            lines.append(f"Stats: {proved}/{total} proved | {cycles} cycle | {pruned} pruned | {failed} failed | {pending} pending")

            shortcuts = [e for e in self._entries.values() if e.proved_by == "shortcut"]
            if shortcuts:
                lines.append("\n## Cross-branch shortcuts")
                for s in shortcuts:
                    lines.append(f"- `{s.name}` ←uses← `{s.import_path}`")

            return "\n".join(lines) + "\n"

    def render_mermaid(self) -> str:
        """Render the proof DAG as a Mermaid flowchart.

        Each node shows: short ID, name, and a snippet of the signature.
        Nodes are styled by status. Edges show parent→child (depends-on).
        """
        with self._lock:
            if not self._root_id:
                return "```mermaid\nflowchart TD\n  empty[No lemmas]\n```\n"

            lines = ["```mermaid", "flowchart TD"]

            # Define nodes — use text status markers (emojis break some renderers)
            status_marker = {
                LemmaStatus.PROVED: "PROVED", LemmaStatus.PROVING: "ACTIVE",
                LemmaStatus.CONTINGENT: "WAITING", LemmaStatus.PENDING: "pending",
                LemmaStatus.FAILED: "FAILED", LemmaStatus.PRUNED: "pruned",
                LemmaStatus.CYCLE: "CYCLE",
            }
            # Node shapes: proved=stadium, active=hexagon, others=rectangle
            for entry in self._entries.values():
                node_id = entry.id[:8]
                indeg = self._indegree.get(entry.id, 0)
                sig_snippet = self._sig_snippet(entry.statement, max_len=40)
                indeg_label = f" in:{indeg}" if indeg > 1 else ""
                marker = status_marker.get(entry.status, "")
                label = f"{entry.name}{indeg_label}<br/>{sig_snippet}<br/>[{marker}]"
                mid = f"n{entry.id}"
                lines.append(f"    {mid}[\"{label}\"]")

            # Define edges
            for entry in self._entries.values():
                for child_id in entry.children:
                    if child_id in self._entries:
                        lines.append(f"    n{entry.id} --> n{child_id}")

            # Style nodes by status
            style_map = {
                LemmaStatus.PROVED: "fill:#2d6,stroke:#1a4,color:#fff",
                LemmaStatus.PROVING: "fill:#48f,stroke:#36c,color:#fff,stroke-width:4px",
                LemmaStatus.CONTINGENT: "fill:#26c,stroke:#14a,color:#fff",
                LemmaStatus.PENDING: "fill:#eee,stroke:#999",
                LemmaStatus.FAILED: "fill:#e44,stroke:#a22,color:#fff",
                LemmaStatus.PRUNED: "fill:#aaa,stroke:#666,color:#fff",
                LemmaStatus.CYCLE: "fill:#f90,stroke:#c60,color:#fff",
            }
            for status, style in style_map.items():
                for e in self._entries.values():
                    if e.status == status:
                        lines.append(f"    style n{e.id} {style}")

            lines.append("```")
            return "\n".join(lines) + "\n"

    @staticmethod
    def _sig_snippet(statement: str, max_len: int = 40) -> str:
        """Extract a short readable snippet from the statement for node labels."""
        if not statement:
            return ""
        # Get the return type (after last ':' before ':= by')
        body_idx = statement.find(":= by")
        if body_idx == -1:
            body_idx = len(statement)
        # Find the conclusion (last ':' that's not inside parens)
        depth = 0
        last_colon = -1
        for i in range(body_idx):
            c = statement[i]
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
            elif c == ':' and depth == 0:
                last_colon = i
        if last_colon > 0:
            snippet = statement[last_colon + 1:body_idx].strip()
        else:
            snippet = statement[:body_idx].strip()
        # Truncate
        if len(snippet) > max_len:
            snippet = snippet[:max_len - 3] + "..."
        return snippet

    def _render_node(self, entry_id: str, indent: int, lines: list[str], visited: set):
        if entry_id in visited:
            entry = self._entries.get(entry_id)
            label = entry.name if entry else entry_id
            lines.append(f"{'│   ' * indent}├── {label} (circular ref)")
            return
        visited.add(entry_id)

        entry = self._entries.get(entry_id)
        if not entry:
            lines.append(f"{'│   ' * indent}├── {entry_id} (missing)")
            return

        if entry.status == LemmaStatus.CYCLE and entry.cycle_ancestor_id in self._entries:
            status_icon = f"⟳ → {self._entries[entry.cycle_ancestor_id].name}"
        else:
            status_icon = {
                LemmaStatus.PROVED: "✅",
                LemmaStatus.CYCLE: "⟳",
                LemmaStatus.PRUNED: "✗ pruned",
                LemmaStatus.FAILED: "✗✗ failed",
                LemmaStatus.PENDING: "⏳",
                LemmaStatus.PROVING: "🔨",
                LemmaStatus.CONTINGENT: "⏸ waiting",
            }[entry.status]

        prefix = "│   " * indent
        connector = "├── " if indent > 0 else ""
        lines.append(f"{prefix}{connector}{entry.name} {status_icon}")

        for child_id in entry.children:
            self._render_node(child_id, indent + 1, lines, visited)

    # ─── Internal helpers ────────────────────────────────────────────────────

    def _has_proved_sibling(self, entry: LemmaEntry) -> bool:
        if not entry.parent_id:
            return False
        parent = self._entries.get(entry.parent_id)
        if not parent:
            return False
        for sibling_id in parent.children:
            if sibling_id == entry.id:
                continue
            sibling = self._entries.get(sibling_id)
            if sibling and sibling.status == LemmaStatus.PROVED:
                return True
        return False


    # ─── Signature utilities ─────────────────────────────────────────────────

    @staticmethod
    def compute_signature_hash(text: str) -> str:
        """Compute hash from a theorem's type signature (name-independent).

        Strips the declaration keyword + name so that two theorems with the
        same parameters and return type but different names produce the same hash.
        """
        stripped = text.strip()
        # Remove "theorem <name>" / "def <name>" / "lemma <name>" prefix
        match = re.match(
            r'(?:private\s+)?(?:noncomputable\s+)?(?:theorem|def|lemma)\s+\S+', stripped)
        if match:
            stripped = stripped[match.end():]
        # Remove body (everything from ':= by' onwards)
        for marker in [':= by', ':= fun', ':= ⟨', ':=']:
            idx = stripped.rfind(marker)
            if idx != -1:
                stripped = stripped[:idx]
                break
        normalized = re.sub(r'\s+', ' ', stripped).strip()
        return hashlib.sha256(normalized.encode()).hexdigest()[:16]
