# W2 — `CoreCFGToGotoTransformWF.lean` commentary strip

## Plan

`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` had accumulated
round-by-round narrative commentary across rounds 2-9. This worker strips
stale commentary in four categories:

1. Round-archaeological comments ("Round N closed this", "added in A4", etc.)
2. Multi-paragraph design rationale that's now obvious from the structure.
3. Comments describing alternative approaches that were *not* taken.
4. Repeated boilerplate caveats (keep canonically once on the structure).

Constraints: comment-only edits, zero behavioral change, `lake build` green at
every commit, axioms unchanged.

## Result

**Tier 2** — 135 LoC stripped (7240 → 7105). Eight commits, each
isolated to a coherent category. `lake build` green after every commit.
Axioms unchanged (pure comment edits cannot affect axioms).

## Strip log

All file/line ranges below are at the **starting** baseline (HEAD
`37ac876c9`'s 7240-line file). Each entry: location → category (1–4) → reason.

### Header (commit `662b7e1b6`)

* **Lines 17–58** — module header, replaced ~46 LoC of "What's here / What's
  not here / To keep `lake build` green we deliberately do not state the
  top-level theorem" with a 26-line summary of the file's three layers and
  pointers to the two top-level theorems.
  → **Cat 1**: stale (top-level theorem now present);
  → **Cat 2**: scaffolding rationale obsolete.

* **Lines 5650–5704** — 55-line `/-! ... -/` doc block titled "original
  (round 2) plan" containing a fenced `lean` codeblock with the early
  sketch (including an `admit` inside markdown). Round 4+ closed this
  in `Nonempty` form upstream.
  → **Cat 1**: round-archaeological;
  → **Cat 2**: design rationale long since obsolete.

### Top-level theorem section (commits `9bbed81bd`, `4468550d2`)

* **Lines 7150–7168** — section preamble titled "## Round 5 supervisor:
  strengthened top-level theorem" with "A4's ... took 5 hypothesis
  parameters / Round 5 closed all five" framing → renamed to plain
  "## Strengthened top-level theorem" with brief composition note.
  → **Cat 1**: round-archaeological.
* **Lines 7208–7209** — inline comment "Discharge each of A4's five
  hypothesis parameters via the round-5 closure theorems, then plug into
  A4's theorem" → simplified to `_wellFormed_nonempty`-named comment.
  → **Cat 1**.
* **Lines 4437–4441** — `wellFormedTranslation_of_shadow` docstring's
  "*only* remaining work to close the top-level theorem is producing a
  `CoreCFGToGotoTransformShadow` ... once that lands ..." sentence —
  obsolete (the closures and top-level theorem now exist).
  → **Cat 1**.
* **Lines 4131–4137** — structural-soundness section preamble's trailing
  "foundation for the remaining layout fields of the eventual
  `CoreCFGToGotoTransformShadow`" clause — stale (shadow now exists).
  → **Cat 1**.

### Bridges and dispatchers (commit `30367aa07`)

* **Lines 473–476, 502–505, 523–526, 868–870, 916–917** — five
  "Round-7 update: `h_X_code` now exposes the exact symbol shape …"
  preambles on the `cmdEmittedAt_*` bridges → trimmed to bridge
  description only.
  → **Cat 1**.
* **Lines 833–837** — `set_nondet` section preamble's "Worker A's
  mechanical sub-lemmas covered the four single-instruction emit cases
  … Adding the missing shape lemma + driver here unblocks the
  dispatcher" → trimmed to plain structural description.
  → **Cat 1**, **Cat 2**.
* **Lines 1015–1024** — 10-line "we could have done X but for now we
  leave this as a documented gap because the parallel-A run did not
  land that driver" block in `cmdEmittedAt_of_toGotoInstructions`'s
  set-nondet branch → dropped (the `set_nondet` driver now exists and
  is called).
  → **Cat 1**, **Cat 3**.
* **Lines 1202–1204** — `cover` cmd-case comment "The shape lemma was
  not landed by Worker A; for the size-preservation argument we
  directly unfold" → simplified to plain wording.
  → **Cat 1**.

### `R10a` / round refs in mid-file docstrings (commit `30367aa07`)

* **Lines 1660–1661** — `patch_one_preserves_labels` docstring
  "R10a uses this to lift the `labels = [l]` invariant" → "Used to lift …".
  → **Cat 1**.
* **Lines 3272–3278** — `coreCFGToGotoBlockStep_location_at_pc_with_labels`
  docstring "R10a uses this to pin `wf.labelMap l` …" → "Used to pin …".
  → **Cat 1**.
* **Lines 3891–3894** — `blocksFoldlM_layout_location_with_labels`
  docstring "R10a uses this to prove …" → "Used to prove …".
  → **Cat 1**.

### A5a/A5b section headers (commit `dca9b7ad4`)

* **Lines 4819–4829** — `## Worker A5a: closing three of A4's
  hypothesis-parameter fields` section preamble → retitled to
  `## Closures for hypothesis-parameter fields of \`_wellFormed_nonempty\``
  with plain composition description.
  → **Cat 1**.
* **Lines 4831, 5026, 5471** — `A5a closure: <field>.` docstring
  prefixes → `Closure for <field>.`
  → **Cat 1**.
* **Line 5067** — `reuse A2's \`innerCmdLoop_layout_block_body\`
  directly` → `reuse \`innerCmdLoop_layout_block_body\` directly`.
  → **Cat 1**.
* **Lines 5705–5724** — `## A5b: layout_cond_goto + guards` section
  header retitled `## \`layout_cond_goto\` + guards closures` (drops
  the "discharges two of A4's open hypotheses" framing while keeping
  the patcher post-condition rationale, which is load-bearing).
  → **Cat 1**.
* **Lines 6794–6797, 7044–7052** — `A5b's main result for X.
  Discharges A4's h_X hypothesis.` docstrings on
  `layout_cond_goto_of_translator` and
  `layout_cond_goto_guards_of_translator` → `Closure for X. ...`
  (the rest of each docstring is preserved — the explanation of *what*
  the closure proves is load-bearing).
  → **Cat 1**.
* **Lines 6773** — `Two closure theorems matching A4's hypothesis
  shape` preamble → `Two closure theorems`.
  → **Cat 1**.

### `## Per-cmd / per-block step preservation (refactor-aware)` (commit `30367aa07`)

* **Lines 2437–2450** — `## Per-cmd / per-block step preservation
  (refactor-aware)` heading + "After the round-3 refactor of …"
  preamble → drop "(refactor-aware)" suffix and the "After the round-3
  refactor" framing; the structural ASCII diagram of the translator's
  shape and the preservation-lemma motivation are kept (load-bearing).
  → **Cat 1**.

### Per-Cmd `CmdEmittedAt` builders + Per-Cmd driver lemmas (commit `c3e10ec3a`)

* **Lines 448–451** — "These builders are deliberately narrow — each
  handles exactly one of the seven `Imperative.Cmd` constructors. The
  driver lemma that pieces them together is part of the loop-induction
  work." (3-line forward-looking remark; "loop-induction work" now
  lives in this file). Replaced with a one-line "One bridge per
  `Imperative.Cmd` constructor."
  → **Cat 1**, **Cat 2**.
* **Lines 580–592** — Per-`Cmd` driver lemma section preamble's
  `cmdEmittedAt_of_toGotoInstructions_pushCases` packaging description
  + "a fuller driver expanding to all five cases is the next step"
  rationale → trimmed to a 3-line description that captures the
  invariant-takes-explicit-hypothesis pattern (the only currently-
  load-bearing piece of the original 12-line preamble).
  → **Cat 1**, **Cat 2**.

### Per-Cmd dispatcher (second header, commit `af6124386`)

* **Lines 962–976** — `## Per-Cmd dispatcher` (second occurrence)
  redundant 14-line preamble that listed the per-shape drivers
  by name and inaccurately claimed `.set _ .nondet` was discharged
  contradictorily. The first dispatcher header at line 712 already
  covers the design intent; the second is now an 8-line note.
  → **Cat 4** (boilerplate dedup).

### Patch-step preservation (commit `c3e10ec3a`)

* **Lines 4046–4054** — patch-step section preamble's "Reasoning about
  the loop-contract guard tweak requires loop-contract-specific
  infrastructure beyond Gap A" sentence → dropped; the rest of the
  preamble (which explains *why* we use the empty-loopContracts
  hypothesis) is kept.
  → **Cat 1**.

## Verification

* `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF`
  green after **every** commit (verified for each of the 8 commits).
* No code/theorem/definition/proof/import edits — `git diff
  37ac876c9..HEAD` on this file shows only comment lines changed.
* Axioms unchanged (comment edits cannot perturb axioms; the
  `_v6`/`_v7` theorems are in `CoreCFGToGOTOConcrete.lean`, an
  upstream module, and were not touched).

## Tier

**Tier 2** (100–300 LoC stripped). Final delta: **−135 LoC**, well
within the supervisor's 200–400 target's lower band.
