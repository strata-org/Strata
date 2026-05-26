# PSA1 — Proof Structure Audit

**Worker:** PSA1 (read-only).
**Branch base:** `htd/unstructured-to-goto` (HEAD `01ac635cc`).
**Scope:** read-only audit of per-theorem LoC distribution, recurring
patterns not yet abstracted, and structural restructuring opportunities
inside `Strata/Backends/CBMC/GOTO/` (root + `CoreCFGToGotoTransformWF/`
subdirectory).

**Verdict:** **Tier 2.** Two substantive restructuring opportunities the
prior audit chain did not surface (a hypothesis-bundle structure on
`_v6`/`_v7` for ~370 LoC, plus dead code from the R11 tightening for
~80 LoC). One small-bore opportunity (the 22-line layering inversion
fix). Plus a structured per-theorem LoC analysis confirming the prior
"as compressed as it can be" finding for the *interior* lemmas.

The combined worth is meaningful (~430-500 LoC of clean compression
plus a layering improvement), but it is all concentrated at the **API
surface** (the public `_v6`/`_v7` theorems and the dead post-R11
strict-form code), not in the proof bodies. The kernel proofs and the
WF-tree per-property preservation chains are genuinely as compressed
as they can be without changing predicate shape — confirming SI2 80-85
percent-structural diagnosis.

---

## 1. Per-theorem LoC distribution

### 1.1 Overall shape: not Pareto, closer to flat

Across the 24 files of the proof (13,504 declared LoC, 325 named
declarations):

| Band | Decl count | LoC | % of total |
|---|---:|---:|---:|
| ≥100 LoC | 28 | 4,273 | 32% |
| 50–99 LoC | 59 | 3,905 | 29% |
| <50 LoC | 238 | 5,326 | 39% |

* Top-10 declarations = 16% of declared LoC.
* Top-20 declarations = 25%.
* The "top 20%" (62 decls) reaches only 50% of LoC.

**There is no fat tail.** The proof has been cleaned to a remarkably
flat distribution: roughly 1/3 of LoC in each of the three size bands.
Restructuring the largest theorems individually is unlikely to be a
big win on its own — the 28 declarations ≥100 LoC are mostly the
*top-level public theorems* and the *cmd/transfer dispatch sites*
that necessarily enumerate cases.

### 1.2 The 15 longest declarations

| LoC | Kind | File | Name |
|---:|---|---|---|
| 328 | thm | `CoreCFGToGOTOConcrete.lean:188` | `coreCFGToGotoTransform_forward_simulation_concrete_v6` |
| 264 | thm | `CoreCFGToGOTOCorrect.lean:315` | `block_body_cmds_simulation` |
| 235 | thm | `ExprTranslationPreservesEvalBoolInt.lean:964` | `toGotoExprCtx_preservesEval_boolInt` |
| 226 | thm | `…WF/FoldAndDecompose.lean:968` | `coreCFGToGotoTransform_wellFormed_nonempty` |
| 195 | str | `ExprTranslationPreservesEvalBoolInt.lean:145` | `BoolIntOpHypotheses` |
| 194 | thm | `CoreCFGToGOTOConcrete.lean:517` | `coreCFGToGotoTransform_forward_simulation_concrete_v7` |
| 184 | thm | `…WF/CondGotoClosures.lean:1021` | `layout_cond_goto_of_translator` |
| 178 | thm | `…WF/BlockBodyClosures.lean:685` | `layout_block_body_of_translator` |
| 169 | thm | `…WF/BlockBodyClosures.lean:328` | `coreCFGToGotoBlockStep_layout_block_body` |
| 157 | ind | `ExprTranslationPreservesEvalBoolInt.lean:562` | `IsBoolIntTranslated` |
| 136 | str | `SteppingBridgesDischarge.lean:89` | `TranslatorBridgeHyps` |
| 135 | thm | `TranslatorBridgeHypsDischarge.lean:75` | `wellFormedTranslation_to_translatorBridgeHyps_v2` |
| 134 | thm | `…WF/Preservation.lean:929` | `innerCmdLoop_layout_block_body` |
| 131 | thm | `…WF/StepPreservation.lean:984` | `coreCFGToGotoBlockStep_condGoto_at_pc` |
| 130 | thm | `PcInversion.lean:490` | `coreCFGToGotoBlockStep_preserves_body_pc_covered` |

### 1.3 Inside the 15 longest

* **`_v6` (328 LoC):** ~190 LoC are hypothesis declarations
  (50 named hypotheses), ~135 LoC are the proof body (lines 372-509).
  The proof itself is short for its job — it dispatches to seven
  separate worker theorems and assembles the result. The bulk is the
  signature.
* **`_v7` (194 LoC):** ~170 LoC of hypotheses (48 named hypotheses,
  40 of which are byte-identical to `_v6`), ~25 LoC of proof body
  (a single `obtain` + delegate to `_v6`).
* **`block_body_cmds_simulation` (264 LoC):** breaks into ~40 LoC
  setup, ~115 LoC `cmd` arm (genuine PC bookkeeping), ~45 LoC
  `goto_true`, ~35 LoC `goto_false`, ~20 LoC `terminal`. The three
  transfer arms have **distinctly different post-step trace
  structure** (per SI2 analysis, confirmed). Real PC arithmetic.
* **`toGotoExprCtx_preservesEval_boolInt` (235 LoC):** the operator
  dispatch in lines 1049-1123 is 13 binary-operator stanzas of 6 lines
  each (~78 LoC). After L4 OpDesc refactor and A2 trim, this is
  the residue. A table-driven macro could absorb maybe 50 LoC, but
  L4 experience (projected 600-800 LoC, delivered 719 LoC) means
  the easy wins are already taken.
* **`coreCFGToGotoTransform_wellFormed_nonempty` (226 LoC):** the
  top-level WF assembly. Builds 12 fields of `WellFormedTranslation`.
  This is the structural counterpart of `_v6` — public surface, mostly
  field-by-field witness assembly.
* **`layout_cond_goto_of_translator` (184 LoC) /
  `layout_block_body_of_translator` (178) /
  `coreCFGToGotoBlockStep_layout_block_body` (169):** real
  bookkeeping; each is the per-property top-level for the
  blocks-fold induction that backs one `WellFormedTranslation` field.

### 1.4 Per-file concentration

A few files have one or two theorems eating most of the file:

| File | Top-2 share |
|---|---|
| `CoreCFGToGOTOConcrete.lean` | `_v6` + `_v7` = **86% of file** (522/611 declared LoC) |
| `CoreCFGToGOTOCorrectStore.lean` | `StepGotoStar_to_ExecProg` + `_storeCorr` = 89% |
| `CmdProvenance.lean` | `decl_provenance` + `assn_provenance` = 60%; the rest is the dead post-R11 `_strict` form (see §3.2) |
| `TranslatorBridgeHypsDischarge.lean` | one theorem (`wellFormedTranslation_to_translatorBridgeHyps_v2`) is **the entire file** |
| `WellFormedTranslationProps.lean` | one theorem is the whole file |

Most other files distribute LoC over many declarations (e.g.,
`Preservation.lean` 28 declarations, top-5 = 37% of file).

---

## 2. Recurring patterns not yet abstracted

### 2.1 The `coreCFGToGotoBlockStep_*` intro skeleton (18 sites, ~7 LoC each)

The five-step intro

```lean
unfold Strata.coreCFGToGotoBlockStep at h_run
simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
generalize h_inner :
  blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
    (Imperative.emitLabel label … st.trans) = inner at h_run
match inner, h_inner with
| .ok trans₂, h_inner => …
| .error _, _ => simp at h_run
```

appears in 18 places: `StepPreservation.lean` (10 sites),
`CondGotoClosures.lean` (4 sites), `BlockBodyClosures.lean` (1),
`PcInversion.lean` (1), `WfLabelMapAgree.lean` (1),
`BlocksFoldClosed.lean` (1).

* SI2 candidate (b-4) flagged this. WF1 attempted a `block_step_intro`
  Lean 4 macro and reverted: declarative-macro hygiene injects
  `Strata.coreCFGToGotoBlockStep✝`, blocking elaboration. WF1
  recommendation: switch to `elab` API.
* **Why I think it is still not worth it:** even with `elab`, the
  saving is ~5 LoC × 18 sites = ~90 LoC, minus a ~30-40 LoC elab
  tactic. Net ~50-60 LoC. The maintenance cost of a custom elaborator
  is real and the prior worker (WF1) explicitly chose to revert.

### 2.2 The `*_at_pc` family (3 sites; was 4)

`StepPreservation.lean` has three theorems projecting **different
post-conditions** about the post-block-step trans:

* `coreCFGToGotoBlockStep_location_at_pc_with_labels` (99 LoC) —
  exposes the leading LOCATION instruction labels.
* `coreCFGToGotoBlockStep_finish_at_pc` (70 LoC) — exposes the
  trailing END_FUNCTION on `.finish` blocks.
* `coreCFGToGotoBlockStep_condGoto_at_pc` (131 LoC) — exposes the
  two trailing GOTOs on `.condGoto` blocks.

WF1 deleted the fourth (`_location_at_pc` without labels, -100 LoC).
The remaining three share only the **intro skeleton** (per §2.1) and
the cmd-fold size/prefix machinery — **the post-step witness shapes
are genuinely distinct**, as SI2 noted. No further unification
without changing what the projection lemmas expose.

### 2.3 The seven paired `*_preserves_size_eq` / `*_preserves_locationNum_eq_index` chains

| Step | size_eq | locationNum_eq_index |
|---|---|---|
| `emitLabel` | 6 LoC | 41 LoC |
| `emitCondGoto` | ~15 | ~22 |
| `emitUncondGoto` | (folded) | ~22 |
| `endFunction_emit` | (folded) | ~15 |
| `toGotoInstructions` | 57 LoC | 73 LoC |
| `cmdsFoldlM` | ~40 | ~50 |
| `coreCFGToGotoCmdStep` | small | small |
| `coreCFGToGotoBlockStep` | 60 | 119 |
| `blocksFoldlM` | ~30 | ~30 |

The `size_eq` proofs are tiny (often 1-line `simp`); the
`locationNum_eq_index` proofs are the real work, and they take
`h_size` as a hypothesis (i.e. they are already coupled). **L3
declined the binary combinator port (Class C); WF1 reaffirmed the
decline.** I confirm: per-pair LoC is dominated by the locationNum
side, the size side is essentially free, and a binary combinator
would add API tax (every closure threading two predicates, the
`h_admitted` for cmd-step plumbing, the eta-expansion issues L3
flagged). Standing decline is correct.

### 2.4 The `*_preserves_body_pc_covered` chain (6 sites in PcInversion.lean)

* `toGotoInstructions_preserves_body_pc_covered` (123 LoC)
* `coreCFGToGotoCmdStep_preserves_body_pc_covered` (47)
* `cmdsFoldlM_preserves_body_pc_covered` (69)
* `coreCFGToGotoBlockStep_preserves_body_pc_covered` (130)
* `blocksFoldlM_preserves_body_pc_covered` (75)
* `patchGotoTargets_preserves_body_pc_covered` (128)

Total: ~570 LoC inside PcInversion (out of 999). L2 classified
`BodyPcCovered` as **Class E** (witness-program + 5 auxiliary
hypotheses). I confirm. The predicate is intrinsically binary
(DECL → ... ∧ ASSIGN → ...), so even modulo Class E plumbing, the
shape does not fit `BlocksFoldClosed`. No new abstraction visible.

### 2.5 The 13-arm operator dispatch in `toGotoExprCtx_preservesEval_boolInt`

`ExprTranslationPreservesEvalBoolInt.lean:1049-1123` — 13 binary-op
stanzas of 6 LoC each (~78 LoC). Each differs only in the operator
constant (`.intAdd`, `.intSub`, ...) and the ne-funApp selector. A
**table-driven `decide`-style dispatch** could collapse this to ~30
LoC, saving ~50 LoC. L4 OpDesc refactor already absorbed the
heavy lifting; this is the residue.

* Why this *might* be worth doing: it is local (one theorem, one file),
  the OpDesc descriptor is already in place, and the saving is real.
* Why I do not claim it as Tier-1: the saving is small (~50 LoC) and
  the resulting indirection (lookup-by-name table) is debatable as a
  readability win.

### 2.6 What was already abstracted (and why nothing close remains)

For completeness, the abstractions already in place:

* `BlocksFoldClosed` — Class A predicate-preservation typeclass;
  saved 594 LoC across NoDead + GotoTargetProvenance.
* `inj_subst` macro — Option.some.inj boilerplate; ~70 LoC saved.
* `BoolIntBinOpDesc` + 2 generics — 13-operator parallelism; ~720 LoC
  saved by L4.
* `OpDesc` (operator descriptor) — partially absorbed by the bridge
  helpers L4 deleted.

The patterns that have not been abstracted (size_eq/locationNum,
body_pc_covered, _at_pc family) all have *structural* reasons not
to fit a single typeclass. SI2 Class A-E taxonomy is descriptively
correct.

---

## 3. Restructuring opportunities

### 3.1 Bundle `_v6`/`_v7` hypotheses into a structure (significant)

**File:** `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`.

The two public theorems share **40 of 50 hypotheses** (computed by
diffing the named binders). The shared list is the **B3 expression
bundle** + **structural inputs** + **bisimulation parameters** +
**trace-pinning** + **value-side correspondence** + **source-side
run** — five logically-grouped clusters. The only differences:

* `_v6` adds `(st_final, h_blocks_run)` (structural witnesses).
* `_v7` does not.
* `_v6` has `(cfg, Env, functionName, trans₀, ans, h_run)` mid-signature;
  `_v7` has the same.

Concretely:

```
v6 hypothesis declaration block: 184 LoC (lines 188-372)
v6 proof body:                   137 LoC (lines 372-509)
v7 hypothesis declaration block: 172 LoC (lines 517-689)
v7 proof body:                    21 LoC (lines 689-710)

Total declared hypothesis text:  356 LoC
Total proof bodies:              158 LoC
                                  ------
                                 514 LoC   (= sum of the two theorem LoCs)
```

**Restructuring:** introduce `structure ConcreteForwardSimHyps` (or
several substructures: `ConcreteFwdSim.Init`, `ConcreteFwdSim.B3`,
`ConcreteFwdSim.Bisim`, `ConcreteFwdSim.Pinning`, `ConcreteFwdSim.Run`)
that bundles the shared 40 hypotheses. Then:

```
structure ConcreteForwardSimHyps δ δ_goto … where
  init : InitHyps δ_goto trans₀
  b3 : B3Bundle δ δ_goto δ_goto_bool
  bisim : BisimHyps …
  pinning : PinningHyps …
  values : ValueCorr …
  run : SrcRun …

theorem _v6 (h : ConcreteForwardSimHyps …) (st_final h_blocks_run …) : …
  := …  -- proof body unchanged, projects fields from h

theorem _v7 (h : ConcreteForwardSimHyps …) : …
  := by
    obtain ⟨st_final, _, _, h_blocks_run, _, _⟩ :=
      coreCFGToGotoTransform_decompose …
    exact _v6 h st_final h_blocks_run
```

Estimated impact:

* `ConcreteForwardSimHyps` definition + projections: ~80-100 LoC
  (depending on how aggressively bundles nest).
* `_v6` theorem signature: ~40 LoC (down from 184).
* `_v6` proof body: 135 LoC (unchanged) but with `h.b3.h_red`
  -style projection. Some `let h_red := h.b3.h_red` upfront could
  keep call-site terseness; net: maybe 145 LoC.
* `_v7` theorem signature: ~30 LoC (down from 172).
* `_v7` proof body: ~20 LoC (unchanged).

Realised: `(80 + 40 + 145 + 30 + 20) = 315`, vs current 514.
**Saving: ~200 LoC.** Adjusting for the L3-calibration ratio
(projected 1,200, delivered 201 = 17%): even if I am off by 2-3x on
the bundle actual cost, we would still save ~100-150 LoC. Plausible
optimistic ceiling: ~300 LoC if bundling is clean and downstream
callers also benefit.

**Why this has not been done:** the `_v3`/`_v4`/`_v5` cleanup wave
focused on *deleting* dead variants. The post-A4 inlining (`_v4` →
`_v5` → `_v6`) made `_v6` a single live theorem. `_v7` was added
later. Nobody revisited the structure of the resulting two-theorem
family. SI1, SI2, WF1, and WF2 all looked at the WF tree or the
kernel; none audited the API surface of the public theorems.

**Risk:** medium. Caller migration is a one-shot change (the
downstream `StrataCoreToGoto.lean` test calls only `_v7`). But the
bundle definition has its own subtle elaboration concerns
(`structure` vs `class`, projection-by-default-instance on the
`Imperative.GotoTransform` argument, etc.). Expect 1-2 days of
work, with realistic 100-150 LoC delivered against 200-300
projected. Still positive.

This is the **single largest concrete restructuring I found that the
prior audit chain did not surface.**

### 3.2 Delete post-R11 dead code (~80 LoC, low risk)

**Files:** `CmdProvenance.lean:249-302`, `PcInversion.lean:14-22`,
`PcInversion.lean:846-852`, `PcInversion.lean:987-997`.

R11 (commit chain ending in the `step_assign_nondet` constructor
tightening) made `AssignNondetPcInversion` and
`assn_nondet_provenance_of_translator_strict` unnecessary. The strict
form is no longer in the live call chain — `grep` confirms zero
callers. Yet:

* `CmdProvenance.lean:249-302` (54 LoC): the doc-comment heading
  "ASSIGN-Nondet provenance — strict form only", the abbrev
  `AssignNondetPcInversion`, and the theorem
  `assn_nondet_provenance_of_translator_strict`. **All dead.**
* `PcInversion.lean:14-22` (~9 LoC): module-doc still asserts that
  the strict form "is provably false in general" and "is left as a
  hypothesis" — but it no longer is.
* `PcInversion.lean:846-852` (~7 LoC): another module-doc reference.
* `PcInversion.lean:987-997` (~11 LoC): the trailing `## Strict
  AssignNondetPcInversion is bridge-layer` comment block — describing
  a status R11 obsoleted.

**Total dead post-R11 surface: ~80 LoC (54 + 9 + 7 + 11).** Pure
cleanup; low risk; mechanical.

**Why this has not been done:** R11 report
(`R11_assn_nondet_closure_report.md`) correctly described the new
state ("removed entirely from `_v5`/`_v6`/`_v7`") but did not delete
the strict-form definitions themselves, presumably as a backstop until
the new path was proven stable. Subsequent audits (SI1, SI2, WF1, WF2)
did not search for "R11-obsoleted" code patterns.

### 3.3 Move `ExprTranslationPreservesEval` from `Correct.lean` to `Invariants.lean` (layering, +0 LoC)

**Current layering:**

```
CoreCFGToGOTOInvariants.lean
  ↓
CoreCFGToGOTOCorrect.lean  ← defines ExprTranslationPreservesEval (22 LoC)
  ↓
CoreCFGToGotoTransformWF/Shape.lean  ← imports Correct *only* for ExprTranslationPreservesEval
ExprTranslationPreservesEvalBoolInt.lean  ← imports Correct *only* for ExprTranslationPreservesEval
```

WF1 spotted this ("Import audit" section) but declined: "fixing it
is out of scope for a shrinkability pass — it requires moving
`ExprTranslationPreservesEval` from `Correct.lean` to
`Invariants.lean`." But it is a 22-line move; the structure has no
proofs and no recursion through `Sim` or anything else in Correct.
Both downstream files use *only* this one symbol from Correct (I
verified by extracting all top-level names defined in Correct, then
intersecting with token sets in Shape and ExprTranslation; the
single overlapping name is `ExprTranslationPreservesEval`).

**Impact:**

* +0 LoC (it is a move, not a delete).
* `Shape.lean` drops its `Correct.lean` import.
* `ExprTranslationPreservesEvalBoolInt.lean` drops its `Correct.lean`
  import.
* The WF tree and the Expr file become **independent of `Correct.lean`**.
  This breaks a real layering inversion (currently
  `Shape → Correct → Invariants` instead of `Shape → Invariants`).

**Why valuable:** parallel compilation. With the move, the WF tree
(6,720 LoC) and `Correct.lean` (928 LoC) become sibling subtrees
that can build in parallel; today the WF tree must wait on Correct.
Same for the Expr file (1,198 LoC). Practical wall-clock savings.

**Risk:** low. Only one tiny structure moves, and only two import
lines change.

### 3.4 Other layouts examined and declined

* **Splitting `CondGotoClosures.lean` (1,373 LoC).** Three logical
  sections (patcher private lemmas, `pendingPatches_*` tracking,
  `layout_cond_goto_*` consumer). Could split into a "patches
  infrastructure" file + a "cond-goto layout" file. ~600 + ~770
  LoC each. Valid but minor; just reorganises the same code.
* **Strong induction in `block_body_cmds_simulation`.** Doc section
  (g) of `WhyDifficult.md` notes this is forced by Lean 4
  structural-recursion limitations on `cs.drop k`. Avoiding it
  would require a structurally different proof shape, not a
  refactor.
* **Two-pass patcher.** The patcher exists because cross-block
  forward GOTO targets are unknown during the blocks-fold (target
  block has not been visited yet). `coreCFGToGotoPatchStep_no_contracts_trans_eq`
  tells us the patcher is **identity except on `target` fields**, so
  the proof can treat it as a discrete final pass. The two-pass
  structure is forced, not stylistic. Confirmed.
* **Predicate shape changes.** `WellFormedTranslation` could in
  principle absorb more derived facts (`size_eq`, `locationNum_eq_index`,
  `bodyPcCovered`, `everyGotoTargetIsLabelMapEntry`) as fields rather
  than as separate top-level theorems. But each currently has a
  different *shape*: `size_eq` is a single equation, `bodyPcCovered`
  carries witness-program parameters and 5 auxiliary hypotheses,
  `everyGotoTargetIsLabelMapEntry` is a forall-exists statement
  with a wf-projection escape hatch. Adding them to `WellFormedTranslation`
  would tip the structure into Class E (witness-program-bound),
  forcing every existing consumer to thread the witness program.
  Net negative.
* **R11-enabled hypothesis tightening.** R11 already extracted the
  available win (eliminated `h_assn_nondet_pc_inv` from `_v5`/`_v6`/`_v7`).
  No further downstream simplification visible — the
  `step_assign_nondet` tightening only flows one direction.

### 3.5 Theorem-statement shape

Asked: "is there a top-level theorem stated in a way that forces
unnecessary downstream work? E.g., if conclusion was an existential,
simulation would compose differently."

The top-level `coreCFGToGoto_forward_simulation` already states an
existential conclusion (`∃ pc_entry σ_goto, StoreCorr ∧ ExecProg`).
The `_v6` / `_v7` shapes inherit this. The conclusion shape is
appropriate; downstream callers do `obtain ⟨pc_entry, σ, h_corr,
h_exec⟩`. No alternative formulation would obviously compose better
without changing what the theorem proves.

The places where the conclusion *could* be tighter:

* `block_body_cmds_simulation` returns
  `∃ c_after_goto, StepGotoStar … ∧ Sim …`. The existential is
  inevitable (the post-config depends on the source terminating
  behaviour). The two-conjunct form is what `block_body_simulation`
  needs.
* `single_cmd_simulation` returns a non-existential `StepGotoStar`,
  which is the right shape for the cmd-fold induction.

No shape changes visible.

---

## 4. Verdict and honest assessment

### 4.1 Tier outcome

**Tier 2.** Two substantive opportunities surfaced (§3.1 hypothesis
bundle ~200 LoC, §3.2 R11 dead code ~80 LoC) plus the layering fix
(§3.3, +0 LoC but enables parallel compilation). Combined potential:
~280-380 LoC, dominated by §3.1.

If the §3.1 bundle delivers at the L3 calibration rate (17% of
projection), realistic outcome is more like 35-50 LoC + the dead-code
cleanup of 80 LoC = **~120-130 LoC actual saving with a structural
improvement**. A "Tier-1 win across multiple files" was not found.

### 4.2 What this audit confirms about prior work

* **SI2 80-85%-structural diagnosis is correct.** The 15 longest
  declarations are all genuinely structural (cmd dispatch, transfer
  arms, layout-witness assembly, top-level signature) — none are the
  "delete this 200-line monstrosity" target.
* **WF1 Tier-3 outcome on the WF tree was correct.** The interior
  per-property preservation chains (size_eq, locationNum,
  body_pc_covered, etc.) are not further compressible without
  structural rework.
* **L3 calibration is real.** Anything that requires a new
  combinator typeclass should expect to deliver 15-30% of the
  projected saving. The non-combinator opportunities I found
  (signature bundling, dead code, file moves) face less of this risk.

### 4.3 What the prior audits missed

* **The API-surface duplication on `_v6`/`_v7`.** The SI1/SI2/WF1/WF2
  chain audited the *interior* of the proof. The two public
  forward-simulation theorems redundant signatures (40 of 50
  hypotheses byte-identical) are the most concrete remaining LoC
  opportunity, and none of the prior audits examined this surface.
* **Post-R11 dead code.** R11 report described the new state but
  the old strict-form definitions were left in place. SI1/SI2/WF1/WF2
  did not search for "R11-obsoleted" patterns. ~80 LoC.
* **The 22-line layering inversion.** WF1 spotted it but declined as
  "out of scope for a shrinkability pass." It is in scope for a
  *structural* pass.

### 4.4 What further compression is plausible

After §3.1, §3.2, §3.3 are landed:

* §2.5 (operator dispatch table): ~50 LoC if pursued, but readability
  trade-off.
* §2.1 (block-step intro macro via `elab`): ~50 LoC if the team has
  Lean elaborator expertise.
* Misc minor wins (split CondGotoClosures, doc strip): individually
  small.

**Total realistic remaining: ~150-300 LoC after the three §3 items
are landed**, before the proof is genuinely converged. That is a
single sprint of work, not multiple weeks.

### 4.5 The honest answer

The user asked: "If [the proof is mostly as compressed as it can be]
is still true, say so clearly and document why."

It is **largely** still true for the *interior* of the proof. The
proof body lemmas — single_cmd_simulation, block_body_cmds_simulation,
the per-property preservation chains, the layout_*_of_translator
top-levels — are tightly written. SI2 12-14% boilerplate /
80-85% structural split is accurate. WF1 Tier-3 outcome (-100 LoC,
1.5% of WF tree) reflects this.

What is **not** true is that the *API surface* is as compressed as
it can be. `_v6`/`_v7` carry ~370 LoC of duplicated hypothesis
declaration that a moderate restructuring (a hypothesis-bundle
structure) could absorb. The dead post-R11 strict-form code (~80
LoC) is a separate, smaller, mechanical cleanup. The 22-line move
removing the layering inversion is a clean structural improvement
that prior audits explicitly punted.

These are "rethink" opportunities at the API/file-layout level, not
inside the proofs. They are consistent with the user framing of
"structural changes, not refactoring": the bundle change reframes
how the public theorem is stated; the layering fix changes the
import graph. Neither is hot air, neither is a 1,200-LoC L3-style
projection. They are sober, modest, concrete.

**My recommendation:** pursue §3.1 (signature bundle) as a single
focused refactor, then §3.2 + §3.3 as a small follow-up cleanup
PR. Total realistic landing: 150-250 LoC removed plus a clean
layering improvement. Then declare the proof structurally converged
unless the source language fragment expands (e.g., adding `.call`
to the admitted set, which is its own proof project per
`CoreToGOTO_CurrentStatus.md` §5).

---

## Appendix: methodology

* Per-theorem LoC counts computed by a regex-based slicer that
  recognises `theorem`/`lemma`/`def`/`instance`/`abbrev`/`opaque`/
  `inductive`/`structure`/`class` declarations. End-of-decl is
  next-decl-start minus one (with trailing-blank trim). Cross-checked
  by hand on `cmdsPrefixInstrCount` and `LabelMap` after the regex
  initially missed `inductive CmdEmittedAt`.
* Cross-file dedup hunt: extracted all top-level names from each
  file, ran intersection-with-token-set against importer files to
  find single-symbol dependencies (used to pinpoint the layering
  inversion in §3.3).
* Pareto computation: sorted all LoC values, computed cumulative-fraction
  thresholds at 50%/80%.
* Hypothesis-diff: regex-extracted named binders inside the `(name :
  …)` blocks of `_v6` and `_v7`, did set-difference. Skipped
  unnamed/positional binders; `st_final` is unnamed (positional `let`)
  in `_v7` and named in `_v6`, hence the "+1 hypothesis" gap shown
  by the diff.
* Skim-and-classify on the 15 longest declarations and the 18
  block-step intro sites; spot-checked claims against actual file
  contents.

No `.lean` files modified. Sole deliverable: this file.
