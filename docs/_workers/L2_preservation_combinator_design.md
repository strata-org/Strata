# L2 — Preservation Combinator Design Audit

**Worker:** L2 (read-only).
**Branch base:** `htd/unstructured-to-goto`.
**Scope:** the five files
[`NoDead.lean`](../../Strata/Backends/CBMC/GOTO/NoDead.lean) (716 LoC),
[`GotoTargetProvenance.lean`](../../Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean) (1116 LoC),
[`PcInversion.lean`](../../Strata/Backends/CBMC/GOTO/PcInversion.lean) (1580 LoC),
[`WfLabelMapAgree.lean`](../../Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean) (698 LoC),
[`CoreCFGToGotoTransformWF.lean`](../../Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean) (7240 LoC).
Total: **11 350 LoC**.

**Verdict:** **Tier 2 — partial dedup for a subset.**
Real saving estimate: **~1 200 – 1 600 LoC** (mostly close to the audit's
*lower* projection of 1 500). The lower number is because PcInversion
and the WF chains don't fit a uniform `P : Array Instruction → Prop`
combinator, but a refined, *structurally* polymorphic `Closed`
typeclass over the 12 translator steps still pays off.

## 1 · The 12-step matrix

The translator decomposes as twelve callable steps; some files cover
all twelve, some skip the patcher chain (because their predicate is
proved over the post-blocks-fold state and bridged to `ans` via a
patcher *property* lemma rather than its own preservation chain).
Coverage matrix (✓ = step has its own `_preserves_X` lemma in the
file; ▲ = covered indirectly through a "trans-eq" rewrite; ⌀ = not
present and not needed; ✗ = not present and would be needed in any
combinator):

| Step | NoDead | GotoTargetProvenance | PcInversion | WfLabelMapAgree | WF.size_eq | WF.locationNum | WF.labelMapBoundedAndInj |
|---|---|---|---|---|---|---|---|
| `toGotoInstructions_preserves_X` | ✓ L163 | ✓ L157 | ✓ L247 | ✓ L153 | ✓ L1202 | ✓ L1335 | ⌀ |
| `coreCFGToGotoCmdStep_preserves_X` | ✓ L266 | ✓ L253 | ✓ L502 | ✓ L237 | ✓ L2466 | ✓ L2482 | ⌀ |
| `cmdsFoldlM_preserves_X` | ✓ L322 | ✓ L302 | ✓ L569 | ✓ L254 | ✓ L2503 | ✓ L2532 | ⌀ |
| `emitLabel_preserves_X` | ✓ L349 | ✓ L332 | ✓ L644 | ✓ L289 | ✓ L1138 | ✓ L1150 | ⌀ |
| `emitCondGoto_preserves_X` | ✓ L367 | ✓ L349 | ✓ L678 | ✓ L346 | ✓ L1408 | ✓ L1417 | ⌀ |
| `emitUncondGoto_preserves_X` | ✓ L383 | ✓ L363 | ✓ L712 | ✓ L366 | ✓ L1439 | ✓ L1448 | ⌀ |
| `endFunction_emit_preserves_X` | ✓ L399 | ✓ L377 | ✓ L746 | ✓ L387 | ✓ L1490 | ✓ L1502 | ⌀ |
| `coreCFGToGotoBlockStep_preserves_X` | ✓ L420 | ✓ L396 | ✓ L789 | ✓ L412 | ✓ L2628 | ✓ L2685 | ✓ L4929 |
| `blocksFoldlM_preserves_X` | ✓ L488 | ✓ L458 | ✓ L957 | ✓ L498 | ✓ L3579 | ✓ L3611 | ✓ L4994 |
| `coreCFGToGotoPatchStep_preserves_X` | ✓ L520 (`_no_contracts`, ▲ via trans-eq) | ✓ L489 (`_no_contracts`, ▲) | ⌀ — bridged through `patchGotoTargets_preserves_full_except_target` | ⌀ — patcher only writes target | ✓ L4080 (▲) | ✓ L4091 (▲) | ⌀ |
| `patchesFoldlM_preserves_X` | ✓ L530 (▲) | ✓ L499 (▲) | ⌀ — same | ⌀ — same | ✓ L4132 (▲) | ✓ L4162 (▲) | ⌀ |
| `patchGotoTargets_preserves_X` | ✓ L547 | ⌀ — actively *broken* (patcher fills targets); a *reverse* lemma `patchGotoTargets_target_some_in_patches` (L704) replaces it | ✓ L1108 (uses `_full_except_target`) | ✓ L563 (uses `_type` + `_labels`) | ⌀ — patcher already known to preserve `size`/`nextLoc` (L350,L374) | ✓ L1621 | ⌀ — labelMap is invariant in patcher |

So the apparent "12 step" pattern is actually closer to **9 + 3**:

* **Steps 1–9** (`toGotoInstructions` … `blocksFoldlM`) form a clean,
  uniform 9-step chain about *the blocks fold*. NoDead, GotoTargetProvenance,
  PcInversion, WfLabelMapAgree, WF.size_eq, WF.locationNum all instantiate
  it. (The `labelMapBoundedAndInj` chain uses only steps 8–9 because the
  cmds-emit helpers don't change the labelMap.)
* **Steps 10–12** (`patchStep` / `patchesFold` / `patchGotoTargets`) are
  *not* a uniform preservation chain. The patcher's per-step lemma reduces
  to `coreCFGToGotoPatchStep_no_contracts_trans_eq` and is mechanical
  (▲); the only *real* work is the final `patchGotoTargets_preserves_X`
  which differs file-by-file (broken in GotoTargetProvenance, full-shape-bridge
  in PcInversion, `type`-bridge in NoDead, `type+labels`-bridge in
  WfLabelMapAgree). This is the "leak" zone.

## 2 · Predicate signatures and unification classes

Sorted from cleanest to leakiest:

### Class A — pure array predicate `P : Array Instruction → Prop`

* **`HasNoDead trans`** (NoDead.lean:83):
  `∀ pc instr, trans.instructions[pc]? = some instr → instr.type ≠ .DEAD`.
  Pure quantification over `trans.instructions`. No CFG, no labelMap, no
  witness program.

That's it. It's a class of one. NoDead is the only file whose
predicate is a function of the array alone.

### Class B — binary predicate `P : Array Instruction × HashMap → Prop`

* **`LocationsTrackLabelMap trans labelMap`** (WfLabelMapAgree.lean:70):
  `∀ pc instr l, trans.instructions[pc]? = some instr →
   instr.type = .LOCATION → instr.labels = [l] → labelMap[l]? = some pc`.
  The labelMap is *also* updated by `emitLabel`, so the combinator must
  let the labelMap evolve.
* **`labelMapBoundedAndInj labelMap nextLoc`** (CoreCFGToGotoTransformWF.lean):
  Doesn't even reference `trans.instructions` — it's a property of
  `(labelMap, nextLoc)`. Lives only on steps 8–9 (block / blocks).

### Class C — array predicate with auxiliary structural side-condition

* **`size = nextLoc` invariant** (CoreCFGToGotoTransformWF.lean:1138 family,
  10 step lemmas). Trivially "array → Prop" but every step lemma also
  needs `h_size : trans.instructions.size = trans.nextLoc` carried.
* **`locationNum_eq_index`** (CoreCFGToGotoTransformWF.lean:1150 family,
  10 step lemmas). Like above but the step lemmas additionally take
  `h_size` as a hypothesis (the `locationNum` of the freshly-pushed
  instruction equals `nextLoc`, which equals `size` only under the
  paired invariant). So this chain is **coupled** with the size_eq
  chain.

### Class D — predicate with a *reverse-direction* witness program

* **`NoGotoHasTarget trans`** (GotoTargetProvenance.lean:74):
  `∀ pc instr, trans.instructions[pc]? = some instr → instr.type = .GOTO →
   instr.target = none`. Looks like Class A — but this predicate is
  *false* on `ans = patchGotoTargets st_final.trans resolved` because the
  patcher fills targets. So the patcher step **breaks** the predicate; the
  file instead proves a *reverse-direction* theorem
  `patchGotoTargets_target_some_in_patches` (L704) and combines it with
  `blocksFoldlM_preserves_no_goto_target`. The combinator can produce
  the 11-step uniform chain through `patchesFoldlM`, but the final
  step needs a different shape.

### Class E — predicate referencing a *target witness program* and three semantic-eval kits

* **`BodyPcCovered δ δ_goto δ_goto_bool trans pgm`** (PcInversion.lean:94):
```
∀ pc instr, trans.instructions[pc]? = some instr →
  (instr.type = .DECL → ∃ inner, CmdEmittedAt … pgm pc inner) ∧
  (instr.type = .ASSIGN →
    (∃ v cv md, CmdEmittedAt … pgm pc (.set v cv md)) ∨
    (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
      CmdEmittedAt … pgm pc_pred (.init v ty (.det e_core) md)))
```
The predicate is **parametrised by**:
  - three semantic-eval objects (`δ`, `δ_goto`, `δ_goto_bool`) that
    `CmdEmittedAt` mentions,
  - a *target program* `pgm` (the post-fold result, used as the witness
    program for the `CmdEmittedAt` resolution chain).
  - and additionally every step lemma needs the auxiliary hypotheses
    `h_admitted` (cmd-by-cmd admittedness), `h_invariant` (size = nextLoc),
    `h_expr_corr` + `h_tx_eq` (expr translation correctness),
    `h_prefix` (the trans's instructions are a prefix of pgm.instructions).
  See [`coreCFGToGotoBlockStep_preserves_body_pc_covered`,
  PcInversion.lean:789–808] for the full per-step parameter list — *eight*
  hypotheses on top of the predicate.

This is the dominant complication: BodyPcCovered's predicate is a
function `(δ, δ_goto, δ_goto_bool, trans, pgm) → Prop`, with the trans
evolving and `pgm` fixed across the entire fold. A combinator
`P : Array Instruction → Prop` cannot capture it without burning the
abstraction on the witness-program plumbing.

## 3 · Concrete combinator API sketch

### 3a · The "Class A" combinator (clean, fits NoDead almost exactly)

```lean
namespace CProverGOTO.PreservationCombinator

/-- Ten-step closure of an `Array Instruction → Prop` under the
    blocks-fold portion of the translator. Patcher closure is handled
    separately because the patcher's behaviour on each predicate
    differs (sometimes preserved trivially, sometimes via a reverse
    lemma). -/
class BlocksFoldClosed (P : Array Instruction → Prop) where
  toGotoInstructions :
    ∀ T fname c trans ans,
      Imperative.Cmd.toGotoInstructions T fname c trans = .ok ans →
      P trans.instructions → P ans.instructions
  cmdStep :
    ∀ fname cmd trans ans,
      Strata.coreCFGToGotoCmdStep fname trans cmd = .ok ans →
      P trans.instructions → P ans.instructions
  cmdsFold :
    ∀ fname cmds trans ans,
      cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = .ok ans →
      P trans.instructions → P ans.instructions
  emitLabel :
    ∀ label srcLoc trans,
      P trans.instructions →
      P (Imperative.emitLabel label srcLoc trans).instructions
  emitCondGoto :
    ∀ guard srcLoc trans,
      P trans.instructions →
      P (Imperative.emitCondGoto guard srcLoc trans).fst.instructions
  emitUncondGoto :
    ∀ srcLoc trans,
      P trans.instructions →
      P (Imperative.emitUncondGoto srcLoc trans).fst.instructions
  endFunction :
    ∀ md fname trans,
      P trans.instructions →
      P (trans.instructions.push (endFunctionInstr md fname trans))
  blockStep :
    ∀ fname lblBlk st st',
      Strata.coreCFGToGotoBlockStep fname st lblBlk = .ok st' →
      P st.trans.instructions → P st'.trans.instructions
  blocksFold :
    ∀ fname blocks st st',
      blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = .ok st' →
      P st.trans.instructions → P st'.trans.instructions

/-- Auto-derive the 7 "leaf" closures (toGotoInstructions, emitLabel,
    emitCondGoto, emitUncondGoto, endFunction, …) from a single
    push-based closure parameter `P_push`:
        P a → (∀ x, x ∈ shape → newOK x) → P (a.push x)
    plus an append-2 variant for `init.det`. -/
def ofPushClosure
    (P : Array Instruction → Prop)
    (h_push : ∀ a x, P a → AcceptableType x.type → P (a.push x))
    (h_append : ∀ a x y, P a →
      AcceptableType x.type → AcceptableType y.type →
      P (a ++ #[x, y]))
    (AcceptableType : InstructionType → Prop) :
    BlocksFoldClosed P := …  -- mechanical assembly of the 9 closures

end CProverGOTO.PreservationCombinator
```

`AcceptableType` is the per-predicate "vocabulary fact" — for NoDead it
is `· ≠ .DEAD`; for the (broken) NoGotoHasTarget predicate it would
be `(· = .GOTO → instr.target = none)` … which forces it to be
indexed by the full instruction, not just the type, so the API has to
be `h_push : ∀ a x, P a → AcceptablePush x → P (a.push x)` with
`AcceptablePush x` covering whatever new-instr fact each predicate
needs.

### 3b · The "Class B" extension (binary `P (instructions, labelMap)`)

```lean
class BlocksFoldClosed₂ (P : Array Instruction → HashMap String Nat → Prop) where
  …  -- emitLabel takes `(trans, labelMap)` ↦ `(trans.push LOC, labelMap.insert label nextLoc)`
  …  -- block-fold needs an extra "label freshness" hypothesis
  …  -- the rest mirror the unary version
```

This works for `WfLabelMapAgree.LocationsTrackLabelMap` and could
also subsume `labelMapBoundedAndInj` — but only if we're willing to
have a separate "two-way" combinator class.

### 3c · The "Class C" extension (predicate + paired structural invariant)

The size_eq / locationNum chains are coupled invariants. The clean
abstraction is:

```lean
class BlocksFoldClosedWith (Inv : Array Instruction → Prop)
    (P : Array Instruction → Prop) where …
```

where every closure carries `Inv trans → Inv ans ∧ (P trans → P ans)`.
But because `Inv = (size = nextLoc)` is itself just another `P`, this
collapses into "prove two `BlocksFoldClosed`s in parallel," which is
fine but doesn't dedup either of them in isolation.

### 3d · Class D (NoGotoHasTarget) — patcher-broken predicate

The combinator gets us through the 9-step blocks-fold chain. The final
patcher step is *not* a closure of `P` and must be replaced by a
*forward-image* lemma like `patchGotoTargets_target_some_in_patches`
(GotoTargetProvenance.lean:704). The combinator API can offer:

```lean
theorem of_blocksFoldClosed (P) [BlocksFoldClosed P]
    {trans₀ ans} (h_init : P trans₀.instructions)
    (h_run : Strata.coreCFGToGotoTransform Env fname cfg trans₀ = .ok ans)
    (h_blocks_only : NoLoopContracts cfg) :
    P (st_final.trans.instructions) := …
```

i.e. *expose the post-blocks-fold form*; let each file extend to `ans`
on its own. NoDead's extension is mechanical (one application of
`patchGotoTargets_preserves_type`); GotoTargetProvenance's extension
is the reverse-direction lemma; PcInversion's is the
`patchGotoTargets_preserves_full_except_target` bridge.

### 3e · Class E (BodyPcCovered) — does NOT fit `Array Instruction → Prop`

PcInversion's `BodyPcCovered` mentions `pgm` and three semantic-eval
objects. Wrapping it as `P (a : Array Instruction) := BodyPcCovered δ
δ_goto δ_goto_bool ⟨a⟩ pgm` works abstractly, but every step lemma
*also* needs `h_admitted`, `h_invariant`, `h_expr_corr`, `h_tx_eq`,
`h_prefix`. Either:

1. Bake them all into the typeclass instance (so every leaf is
   "assuming admittedness, invariant, correctness, prefix, then
   `P trans → P ans`"); but those hypotheses must thread through the
   *fold*, which means the typeclass interface gets ugly fast.
2. Refuse: leave PcInversion *outside* the combinator. Saves nothing.

The CFG-aware hypotheses (`h_admitted`) plus the witness-program
hypothesis (`h_prefix`) are the leaks the audit didn't account for.

## 4 · Per-file LoC saving estimate

I count net LoC after a hypothetical refactor as:

* **Predicate definition + `ofPushClosure` / `ofPushClosure₂`
  application** (≈ 30 LoC).
* **A `BlocksFoldClosed` instance** — 1 line (`instance : BlocksFoldClosed
  HasNoDead := ofPushClosure …`) plus the 5–10 lines giving
  `AcceptablePush`.
* **Patcher bridging** — file-specific, unchanged.
* **Top-level `_of_translator` theorem** — unchanged shape, ~40 LoC.

| File | Current LoC | Per-step lemma count (combinable) | Avg LoC per step lemma | After refactor (est.) | Net saving |
|---|---|---|---|---|---|
| `NoDead.lean` | 716 | 9 (steps 1–9) + 3 patcher | 25–55 | ~360 | **~360** |
| `GotoTargetProvenance.lean` (steps 1–9 are uniform; the rest is the reverse-direction proof + `EveryGotoTargetIsLabelMapEntry` plumbing) | 1116 | 9 | 25–60 | ~720 | **~400** |
| `PcInversion.lean` (Class E — the combinator can't absorb the witness-program plumbing or h_prefix; only steps 1–7 of the 9 are tractable) | 1580 | 7 partially-fitting | 50–110 | ~1450 | **~130** |
| `WfLabelMapAgree.lean` (Class B — needs the binary combinator; if implemented, savings track NoDead) | 698 | 9 | 25–55 | ~470 | **~230** |
| `CoreCFGToGotoTransformWF.lean` size_eq + locationNum chains (steps 1–11 each, coupled) | 7240 (whole file) — chains are ~ 1100 LoC together (L1138–L4268 minus orthogonal lemmas) | 9 + 9 (coupled) | 30–80 | ~700 | **~400** |

**Total estimated saving: ~1 200 – 1 600 LoC**, vs. the audit's
"~600–800 LoC" lower-bound and the optimization analysis's
"~1 500–2 500 LoC" upper-bound.

So the audit's *upper* projection (1 500–2 500) was **optimistic** by
~30–50 % once you account for:

1. PcInversion's witness-program parameter and the 5 auxiliary
   hypotheses on every step lemma. Even with the combinator, these
   must thread through the fold — most of the LoC in PcInversion is
   that threading, not the predicate logic.
2. GotoTargetProvenance's patcher-broken predicate forcing a separate
   reverse-lemma chain.
3. The CoreCFGToGotoTransformWF chains being structural invariants
   that couple to each other; collapsing them in *isolation* leaves
   roughly the same cross-coupling.

The audit's *lower* projection (600–800) is achievable just for
NoDead + the two clean-Class-A halves of the WF file.

## 5 · Verdict — Tier 2

**Refactor a subset, leave the rest alone.** Specifically:

### Worth doing (clean wins, ~700–900 LoC saved)

1. **NoDead.lean**: refactor in full. Class A. Saves ~360 LoC.
2. **GotoTargetProvenance.lean** steps 1–9: refactor through the
   blocks-fold portion only. The reverse-direction patcher lemma
   stays as is. Saves ~400 LoC.
3. **CoreCFGToGotoTransformWF.lean** size_eq chain: refactor.
   Saves ~150–200 LoC. The locationNum chain *also* qualifies but
   shares scaffolding with size_eq, so the marginal gain is smaller —
   another ~150–200 LoC.

### Worth doing only if Class B combinator is stable

4. **WfLabelMapAgree.lean**: refactor through the binary combinator.
   Saves ~230 LoC. Adds API surface (a separate combinator class).
   Net win is positive but smaller per LoC. Recommended after #1–#3
   prove the API.

### Not worth doing

5. **PcInversion.lean**: leave alone. Class E predicate doesn't
   structurally fit, and the value of "look the same as NoDead's
   chain" is undermined by 8 auxiliary hypotheses per step lemma. The
   handful of LoC saved (~130) doesn't justify rebuilding the
   threaded-context machinery.
6. **CoreCFGToGotoTransformWF.lean**'s `labelMapBoundedAndInj` chain:
   only 2 steps (block / blocks), already tight. Nothing to dedup.

### Follow-up worker plan (for Tier-2 execution)

**Worker L3 (suggested):** ~1 day of work.

1. **L3.1 — combinator infra (1 file, ~150 LoC):** create
   `Strata/Backends/CBMC/GOTO/PreservationCombinator.lean` exporting
   `BlocksFoldClosed P` typeclass with the 9 closure obligations,
   plus `ofPushClosure` + `ofAppendTwoClosure` helpers, plus the
   `BlocksFoldClosed → blocksFoldlM_preserves_X` derived theorem.
2. **L3.2 — port NoDead.lean** (single, isolated change). Confirm
   axiom count unchanged, no new hypotheses surface. Establishes the
   API.
3. **L3.3 — port GotoTargetProvenance.lean steps 1–9.** Keeps the
   reverse-direction patcher lemma untouched. Fastest follow-up after
   NoDead because the predicate signature is closest.
4. **L3.4 — extract size_eq closures from CoreCFGToGotoTransformWF.**
   This file is the riskiest because everything else *depends* on it;
   land this last and run a full proof check.
5. **L3.5 — assess WfLabelMapAgree.** If the binary combinator
   `BlocksFoldClosed₂ P` proves uniform with the unary one, port. If
   awkward, leave alone.

**Dependencies:**
- L3.1 → L3.2 → L3.3 (NoDead must compile before GotoTargetProvenance
  reuses the API).
- L3.4 should land independently of L3.2/L3.3; coordinating with
  whoever is touching that file actively.
- L3.5 last, optional.

**Acceptance:**
- Net LoC down by 800+ across the four touched files (NoDead,
  GotoTargetProvenance, WF size_eq, WfLabelMapAgree).
- Axiom counts unchanged on top-level public theorems
  (`no_dead_program_of_translator`, `everyGotoTargetIsLabelMapEntry_of_translator`,
  `coreCFGToGotoTransform_size_eq_and_loc`,
  `labelMap_agree_of_translator`).
- No new sorries.

## 6 · Honest assessment

The audit's qualitative claim is correct: there is a 9-step
byte-for-byte parallel between NoDead, GotoTargetProvenance, and the
size_eq chain. But the audit *under*counted the leaks:

* **PcInversion is structurally different** — Class E with five
  auxiliary hypotheses. Trying to force it into a uniform combinator
  was always going to spend the savings on plumbing.
* **WfLabelMapAgree is binary** — needs a parallel combinator
  class, not the same one.
* The *patcher* is not a uniform 12th step. It's preserved trivially
  for some predicates, *broken* for others (NoGotoHasTarget), and
  bridged through `_full_except_target` for yet others.

So the answer to "is the optimization analysis's 1 500–2 500 LoC
estimate accurate?" is **no** — the saving is closer to **1 200–1 600
LoC**, sitting near the bottom of that range. Still material, still
worth doing for the clean subset. But anyone budgeting time should
plan for a Class A combinator + a Class B combinator + leaving
PcInversion alone, not for one universal `InstrPredicateClosed`.
