"""Fix A regression tests: the syntactic in-file dependency scan + comment
stripper that feed the guide's AUTHORITATIVE transitive-sorry overview.

Three layers, cheapest first:

  1. ``strip_comments`` — PURE Python, no Lean. The lexical port of the Lean
     ``stripComments``/``trimComment`` state machine (nested ``/- -/`` depth +
     ``--`` line/inline comments). If a lemma name appears only inside a comment
     it must NOT survive to the dependency scan, or a commented-out reference
     becomes a phantom edge.

  2. ``thm_depends_on`` / ``get_reachable_theorems`` — parser-only (``split_theorems``
     via itp-interface), NO ``lake build``. Word-boundary matching (``foo`` must
     not match ``foobar`` / ``Foo.foo``), transitive BFS closure over chains and
     mutual blocks, comment-excluded edges, and coverage across decl keywords
     (theorem/lemma/def) and access modifiers (public/private/protected).

  3. ``transitive_sorry_map`` — the full join (edges + module-safe ``#print axioms``
     verdict + sorry positions). This ONE test does a real ``lake build`` (like
     test_module_sorry_oracle), so it is the slow tail; everything above is fast.

Parser/build fixtures are written on the fly into a temp dir under the
``StrataAgent.+`` lean_lib glob and removed in teardown — nothing is checked in.
Run:  cd StrataAgent && python tests/test_dep_scan.py
"""

from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_lean import (
    get_lean_tools,
    strip_comments,
    blank_comments,
    local_sorry_positions,
)

# tests/ -> StrataAgent/ -> repo root (where lakefile.toml lives). The Lean tools
# resolve file_path relative to the repo root, so fixture paths are repo-relative.
STRATA_AGENT = Path(__file__).resolve().parent.parent
REPO_ROOT = STRATA_AGENT.parent

WORK_DIR = STRATA_AGENT / "tests" / "Lean" / "dep_scan_tmp"
FIX_DIR_REL = "StrataAgent/tests/Lean/dep_scan_tmp"
FIX_MOD_PREFIX = "StrataAgent.tests.Lean.dep_scan_tmp"


# ── Parser fixtures (NON-module — no build, just split_theorems) ──────────────
# A transitive chain, a word-boundary trap, a comment-only reference, and a
# mutual block. All proofs are trivially closeable so split_theorems parses them.
CHAIN_SRC = (
    "theorem leaf_lemma (n : Nat) : n + 0 = n := by simp\n\n"
    "-- `leaf_lemma_helper` below is a DISTINCT name; the word-boundary scan\n"
    "-- must not let `leaf_lemma` match inside it.\n"
    "theorem leaf_lemma_helper (n : Nat) : 0 + n = n := by simp\n\n"
    "theorem mid_lemma (n : Nat) : n + 0 = n := by\n"
    "  -- commented reference to leaf_lemma_helper must NOT create an edge\n"
    "  exact leaf_lemma n\n\n"
    "theorem top_lemma (n : Nat) : n + 0 = n := by\n"
    "  /- block comment mentioning mid_lemma should be stripped;\n"
    "     the REAL edge is via the exact below -/\n"
    "  exact mid_lemma n\n"
)

# Decl-keyword + access-modifier coverage (still NON-module so `public` is inert
# but the head parser must still strip it and recover the real name).
MODIFIERS_SRC = (
    "private def helper_def (n : Nat) : Nat := n + 0\n\n"
    "protected lemma helper_lemma (n : Nat) : helper_def n = n := by\n"
    "  unfold helper_def; simp\n\n"
    "theorem uses_both (n : Nat) : helper_def n = n := by\n"
    "  exact helper_lemma n\n"
)


def _rel(name: str) -> str:
    return f"{FIX_DIR_REL}/{name}.lean"


# The itp-interface parser (via split_theorems) resolves repo-relative file
# paths against the PROCESS cwd, so the tests must run from the repo root (where
# lakefile.toml lives). We chdir in setup and restore in teardown.
_PREV_CWD: str = ""


def setup() -> None:
    global _PREV_CWD
    _PREV_CWD = os.getcwd()
    os.chdir(REPO_ROOT)
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)
    (WORK_DIR / "Chain.lean").write_text(CHAIN_SRC, encoding="utf-8")
    (WORK_DIR / "Modifiers.lean").write_text(MODIFIERS_SRC, encoding="utf-8")


def teardown() -> None:
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR, ignore_errors=True)
    if _PREV_CWD:
        os.chdir(_PREV_CWD)


# ══ Layer 1: strip_comments (pure) ════════════════════════════════════════════

def test_strip_comments_line_comment_preserves_newline():
    src = "exact foo\n-- comment mentions bar\nexact baz\n"
    out = strip_comments(src)
    assert "bar" not in out, "line-comment text survived stripping"
    assert "foo" in out and "baz" in out
    # newline structure preserved (the stripper keeps line boundaries)
    assert out.count("\n") == src.count("\n")
    print("✓ test_strip_comments_line_comment_preserves_newline")


def test_strip_comments_inline_comment():
    src = "exact foo -- trailing ref to bar_lemma\n"
    out = strip_comments(src)
    assert "foo" in out, "code before an inline comment must survive"
    assert "bar_lemma" not in out, "inline `--` comment text survived stripping"
    print("✓ test_strip_comments_inline_comment")


def test_strip_comments_nested_block():
    src = "before /- outer /- inner mentions ghost_lemma -/ still comment -/ after\n"
    out = strip_comments(src)
    assert "ghost_lemma" not in out, "nested block comment not fully stripped"
    assert "before" in out and "after" in out, "code around a nested block lost"
    print("✓ test_strip_comments_nested_block")


def test_strip_comments_unterminated_block_is_safe():
    # An unterminated `/-` swallows the rest — must not raise, must drop the name.
    src = "exact real_edge\n/- dangling mentions ghost_lemma\nstill inside\n"
    out = strip_comments(src)
    assert "real_edge" in out
    assert "ghost_lemma" not in out
    print("✓ test_strip_comments_unterminated_block_is_safe")


# ══ Layer 1b: single local-sorry source (pure, position-preserving) ═══════════
# Regression guard for the show_file_state bug: a `sorry` sitting below a block
# comment was reported at the WRONG line (the deleting comment-stripper collapsed
# line numbers), and the word "sorry" appearing in doc-comment prose was counted
# as a real sorry — so a theorem read "proved" while the file still had a sorry.

def test_blank_comments_preserves_line_and_col():
    # Two-line block comment above a `sorry` — blanking must keep the sorry at its
    # ORIGINAL line (deleting the comment would shift it up two lines).
    src = "/- doc\nmore doc -/\ntheorem t : True := by\n  sorry\n"
    out = blank_comments(src)
    assert out.count("\n") == src.count("\n"), "line count changed — positions shift"
    assert len(out) == len(src), "byte length changed — columns shift"
    lines = out.split("\n")
    assert "doc" not in lines[0] and "doc" not in lines[1], "comment text survived"
    assert lines[3] == "  sorry", "the real sorry line must be preserved verbatim"
    print("✓ test_blank_comments_preserves_line_and_col")


def test_local_sorry_positions_ignores_prose_sorry():
    # `sorry` in a doc-comment (and `sorryAx`, `my_sorry`) must NOT be flagged; only
    # the bare tactic token counts, at its true 0-indexed line/col.
    src = (
        "/-! mentions the word sorry in prose\n"
        "and sorryAx and my_sorry too -/\n"
        "theorem t : True := by\n"
        "  sorry\n"
    )
    pos = local_sorry_positions(src)
    assert pos == [{"line": 3, "col": 2}], f"expected one real sorry at line 3: {pos}"
    print("✓ test_local_sorry_positions_ignores_prose_sorry")


def test_local_sorry_positions_word_boundary():
    # Identifiers containing `sorry` are not the tactic; multiple real ones counted.
    src = "def sorry_free := 0\ntheorem a : True := by sorry\ntheorem b : True := by sorry\n"
    pos = local_sorry_positions(src)
    assert len(pos) == 2, f"expected exactly 2 real sorry tokens: {pos}"
    assert all(p["line"] in (1, 2) for p in pos), pos
    print("✓ test_local_sorry_positions_word_boundary")


# ══ Layer 2: dependency scan (parser-only, no build) ══════════════════════════

def test_direct_edge_and_word_boundary():
    """`mid_lemma` uses `leaf_lemma`, NOT `leaf_lemma_helper` (word boundary)."""
    t = get_lean_tools()
    deps = t.thm_depends_on(_rel("Chain"), "mid_lemma")
    assert "leaf_lemma" in deps, f"real edge missing: {deps}"
    assert "leaf_lemma_helper" not in deps, (
        f"word-boundary violated — `leaf_lemma` matched inside `leaf_lemma_helper`: {deps}")
    print("✓ test_direct_edge_and_word_boundary")


def test_comment_reference_is_not_an_edge():
    """`mid_lemma`'s body has a *commented* mention of `leaf_lemma_helper`; the
    comment-stripping scan must not register it. `top_lemma`'s block comment
    mentions `mid_lemma` but the real edge is the `exact` — still exactly one."""
    t = get_lean_tools()
    mid = t.thm_depends_on(_rel("Chain"), "mid_lemma")
    assert "leaf_lemma_helper" not in mid, f"commented name became an edge: {mid}"
    top = t.thm_depends_on(_rel("Chain"), "top_lemma")
    assert top == ["mid_lemma"], f"top_lemma edges wrong (comment leaked?): {top}"
    print("✓ test_comment_reference_is_not_an_edge")


def test_transitive_reachable_closure():
    """top → mid → leaf. The BFS closure from top_lemma must include all three
    (itself + mid + leaf) and must NOT drag in the unrelated leaf_lemma_helper."""
    t = get_lean_tools()
    reach = t.get_reachable_theorems(_rel("Chain"), "top_lemma")
    assert {"top_lemma", "mid_lemma", "leaf_lemma"} <= reach, f"closure incomplete: {reach}"
    assert "leaf_lemma_helper" not in reach, (
        f"unrelated decl pulled into closure: {reach}")
    print("✓ test_transitive_reachable_closure")


def test_leaf_has_no_deps():
    t = get_lean_tools()
    assert t.thm_depends_on(_rel("Chain"), "leaf_lemma") == []
    assert t.get_reachable_theorems(_rel("Chain"), "leaf_lemma") == {"leaf_lemma"}
    print("✓ test_leaf_has_no_deps")


def test_modifier_and_keyword_coverage():
    """def / lemma / theorem with private/protected modifiers must all be parsed
    (name recovered past the modifier) AND participate in the dependency scan."""
    t = get_lean_tools()
    split = t.split_theorems(_rel("Modifiers"))
    assert split.error is None, f"split errored: {split.error}"
    names = {b.name for b in split.blocks}
    assert {"helper_def", "helper_lemma", "uses_both"} <= names, (
        f"modifier-prefixed decls not recovered: {names}")
    # uses_both → helper_lemma → helper_def ; edges must cross the modifiers.
    assert "helper_lemma" in t.thm_depends_on(_rel("Modifiers"), "uses_both")
    assert "helper_def" in t.thm_depends_on(_rel("Modifiers"), "helper_lemma")
    reach = t.get_reachable_theorems(_rel("Modifiers"), "uses_both")
    assert {"uses_both", "helper_lemma", "helper_def"} <= reach, f"closure: {reach}"
    print("✓ test_modifier_and_keyword_coverage")


# ══ Layer 3: transitive_sorry_map (REAL build — the slow tail) ════════════════

def test_transitive_sorry_map_module():
    """End-to-end join: edges + module-safe #print axioms verdict + positions.
    Module fixtures (public decls) so the out-of-module axiom probe can see them.

      leaf_ok    : real proof, no sorry
      leaf_bad   : direct sorry
      root_thm   : exact leaf_ok, then leaf_bad — transitively carries leaf_bad's sorry

    The map must (a) build, (b) mark root_thm NOT done (transitive sorry via
    leaf_bad), (c) list leaf_bad in root_thm's open_deps, (d) NOT list leaf_ok.
    """
    t = get_lean_tools()
    src = (
        "module\n\n"
        "public theorem leaf_ok (n : Nat) : n + 0 = n := by simp\n\n"
        "public theorem leaf_bad (n : Nat) : n + 0 = n := by sorry\n\n"
        "public theorem root_thm (n : Nat) : n + 0 = n := by\n"
        "  have h1 := leaf_ok n\n"
        "  have h2 := leaf_bad n\n"
        "  exact h1\n"
    )
    (WORK_DIR / "TSMap.lean").write_text(src, encoding="utf-8")
    tsm = t.transitive_sorry_map(_rel("TSMap"), ["root_thm"])
    assert tsm.build_ok, f"fixture should build (sorry is a warning): {tsm.build_error}"
    assert "root_thm" in tsm.targets
    tgt = tsm.targets["root_thm"]
    assert tgt.done is False, "root_thm transitively carries leaf_bad's sorry — not done"
    assert "leaf_bad" in tgt.open_deps, f"open dep leaf_bad missing: {tgt.open_deps}"
    assert "leaf_ok" not in tgt.open_deps, f"proven leaf_ok wrongly flagged open: {tgt.open_deps}"
    # leaf_ok on its own is a done target.
    tsm2 = t.transitive_sorry_map(_rel("TSMap"), ["leaf_ok"])
    assert tsm2.targets["leaf_ok"].done is True, "genuinely-proven leaf not marked done"
    # open_sorry_count over the union counts leaf_bad + root_thm (both transitively open).
    assert tsm.open_sorry_count() >= 2, f"expected ≥2 open sorries, got {tsm.open_sorry_count()}"
    print("✓ test_transitive_sorry_map_module")


def test_show_file_state_never_contradicts_itself():
    """The show_file_state bug: a `sorry` under a doc-comment made the RPC report
    the wrong line, so it grouped into NO theorem → every theorem read "proved"
    while the file-level flag said has_sorry_local. With one source, the per-theorem
    breakdown and the file-level flags cannot disagree.

    Module fixture with prose "sorry" in a doc-comment above a real tactic sorry
    (the exact shape of Sandbox/Stub.lean that triggered the bug).
    """
    t = get_lean_tools()
    src = (
        "module\n\n"
        "/-! doc comment: this file exercises the sorry machinery; the word\n"
        "sorry appears here in PROSE and must be ignored by the scanner. -/\n\n"
        "public theorem helper (n : Nat) : n + 0 = n := by\n"
        "  sorry\n\n"
        "public theorem main_vc (n : Nat) : n + 0 = n := by\n"
        "  exact helper n\n"
    )
    (WORK_DIR / "ShowState.lean").write_text(src, encoding="utf-8")
    st = t.show_file_state(_rel("ShowState"))

    by_name = {thm["name"]: thm for thm in st["theorems"]}
    assert "helper" in by_name and "main_vc" in by_name, f"decls missing: {by_name}"
    # The real sorry is inside `helper` (below the prose-sorry doc comment).
    assert by_name["helper"]["has_sorry"] is True, "real sorry in helper not detected"
    assert by_name["helper"]["status"] == "sorry"
    assert by_name["helper"]["sorry_positions"], "sorry position not localized to helper"
    # main_vc has no sorry of its own.
    assert by_name["main_vc"]["has_sorry"] is False, "main_vc wrongly flagged (prose sorry?)"

    # The invariant: file-level count == sum of per-theorem positions, and the
    # has_sorry_local flag agrees with the per-theorem breakdown.
    per_thm_total = sum(len(thm["sorry_positions"]) for thm in st["theorems"])
    assert st["sorry_count_local"] == per_thm_total == 1, (
        f"count disagreement: file={st['sorry_count_local']} per_thm={per_thm_total}")
    assert st["has_sorry_local"] is True
    # No theorem may read "proved" while the file reports a local sorry.
    if st["has_sorry_local"]:
        assert any(thm["has_sorry"] for thm in st["theorems"]), (
            "file has_sorry_local=True but EVERY theorem reads proved — the exact bug")
    print("✓ test_show_file_state_never_contradicts_itself")


if __name__ == "__main__":
    print("=" * 60)
    print("test_dep_scan (comment stripper + dependency scan + sorry map)")
    print("=" * 60)
    setup()
    try:
        # Layer 1 — pure
        test_strip_comments_line_comment_preserves_newline()
        test_strip_comments_inline_comment()
        test_strip_comments_nested_block()
        test_strip_comments_unterminated_block_is_safe()
        # Layer 2 — parser only
        test_direct_edge_and_word_boundary()
        test_comment_reference_is_not_an_edge()
        test_transitive_reachable_closure()
        test_leaf_has_no_deps()
        test_modifier_and_keyword_coverage()
        # Layer 3 — real build (slow tail)
        test_transitive_sorry_map_module()
    finally:
        teardown()
    print("\n✅ All dep-scan tests passed!")
