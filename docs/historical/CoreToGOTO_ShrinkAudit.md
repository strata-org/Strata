# Proof shrinkability audit (2026-05-22)

Audit target: the round-1-through-8 proof closure work for
`coreCFGToGoto_forward_simulation` against the actual translator
`Strata.coreCFGToGotoTransform`. ~17,990 LoC of correctness
infrastructure under `Strata/Backends/CBMC/GOTO/`. This is a
**read-only audit**; no `.lean` files have been modified. The numbers
here measure source-line counts, not Lean kernel work — every theorem
counted as "removable" is removable in the sense that no live consumer
depends on it as of this branch.

## TL;DR

A future cleanup pass could shave roughly **2,500-3,500 LoC** from
the round-6/7/8 deliverables without weakening any actively-consumed
theorem. The two biggest wins are (1) deleting the dead waypoint
versions `_v2` and `_v3` of
`coreCFGToGotoTransform_forward_simulation_concrete` (which no live
consumer or axiom test references — only `_v4` and `_v5` are tested
and `_v5` calls `_v4` directly, skipping `_v2`/`_v3`) for ~440 LoC,
and (2) factoring the literally-parallel
"preservation-through-each-translator-stage" skeletons out of
`NoDead.lean` and `GotoTargetProvenance.lean` into a single generic
combinator for ~600-800 LoC saved across the two files plus another
~140 LoC of patcher lemmas duplicated between
`CoreCFGToGotoTransformWF.lean` and `GotoTargetProvenance.lean`.

## Findings by category

### 1. Dead code

#### 1.1 Unsuffixed v1 theorem and `_v2`/`_v3` waypoints in `CoreCFGToGOTOConcrete.lean`

The active call graph is:

* `_v5` (`CoreCFGToGOTOConcrete.lean:1059-1350`) → axiom-tested at
  `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean:18`.
* `_v5` body (line 1337) calls `_v4` directly.
* `_v4` (lines 761-1010) → axiom-tested at the same file:15.
* `_v4` body builds its own WF + bridge_v2 from scratch — **does
  NOT call `_v3`** despite the v4 docstring claiming it "extends
  v3".
* `_v3` (lines 508-723) is **never called by any live theorem or
  axiom test**. Its body builds its own WF + bridge_v1 from scratch.
* `_v2` (lines 379-468) is **never called by any live theorem or
  axiom test**. Its body delegates to v1.
* The unsuffixed `coreCFGToGotoTransform_forward_simulation_concrete`
  (lines 102-202, "v1") is called only by `_v2` (line 461). With
  `_v2` dead, v1 is dead too.

Verified by:
```
grep -rn "coreCFGToGotoTransform_forward_simulation_concrete" \
    Strata StrataTest 2>/dev/null
```
which finds the v1/v2/v3 names only in v3/v2/v1's own `theorem ...`
header lines, in their respective doc-comment block titles, and in
the v2-body's `exact ...` line (the only live downstream call to v1).

Removable LoC (with their preceding doc comments):

* v1 body + doc: ~205 LoC (lines 22-202 of the file include both).
* v2 body + doc: ~95 LoC (lines 379-468).
* v3 body + doc: ~250 LoC (lines 470-723).
* **Subtotal: ~440 LoC** if we collapse v1+v2+v3.

Caveat: v2 is *partially* preserved by `ConcreteExprCorr` (lines
245-378 inside the v2-prologue doc), which `_v3`/`_v4`/`_v5` all
import via `let h_expr := ConcreteExprCorr.buildExprCorr ...`.
That namespace must stay; only the *theorem statement and proof*
of v2 itself are removable.

#### 1.2 `wellFormedTranslation_to_translatorBridgeHyps` (bridge v1) in `TranslatorBridgeHypsDischarge.lean`

The bridge v1 theorem (`TranslatorBridgeHypsDischarge.lean:113-234`,
~120 LoC) has two callers:

* `wellFormedTranslation_to_translatorBridgeHyps_v2` (the same
  file, line 361).
* `_v3` of the concrete-forward-simulation chain
  (`CoreCFGToGOTOConcrete.lean:702`).

If `_v3` is deleted (per item 1.1 above), bridge_v1 has only one
live consumer (bridge_v2), which uses it as a one-line delegate.
Bridge_v1 could then be inlined into bridge_v2 OR kept as a
private helper at substantially reduced documentation cost.
**~50-100 LoC reducible** depending on inlining strategy.

#### 1.3 `everyGotoTargetIsLabelMapEntry_of_translator` (the wf-form) in `GotoTargetProvenance.lean`

`GotoTargetProvenance.lean:1067-1115` (~50 LoC) is the
"wf-form" of the provenance theorem. It is called by **no active
proof** in the proof chain — `_v5` invokes
`everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`
(the hashmap-keyed form) instead, then bridges to `wf.labelMap`
inline using the caller-supplied `h_labelMap_agree` hypothesis.

The wf-form is referenced only by
`StrataTest/Backends/CBMC/GOTO/GotoTargetProvenanceAxioms.lean:18`
as a smoke test. Removing the smoke-test entry plus the theorem
would save ~50 LoC plus 4 lines of axiom-test boilerplate.

If kept as a "derivative form available to downstream callers
that prefer the wf-keyed shape", the call site comment in
`_v5` (lines 1283-1301) should be updated to mention it as the
recommended path. Today it doesn't.

#### 1.4 Three unused `_h_inj` parameters in `InstructionLookups.lean`

`InstructionLookups.lean:180`, `:232`, `:296` all take
`(_h_inj : Function.Injective nameMap)` but never use it
(underscore-prefix tells Lean it's intentionally unused). The
sole live caller in
`TranslatorBridgeHypsDischarge.lean:365`/`:368`/`:371` passes
`h_inj` to all three.

Removing the three unused parameters and the three call-site
arguments saves ~15 LoC. The hypothesis remains needed by the
*caller* (it's a field of the bridge); only the lookup theorems
themselves don't need it.

#### 1.5 Round-4 `coreCFGToGotoTransform_wellFormed` and `_nonempty` waypoints in `CoreCFGToGotoTransformWF.lean`

`CoreCFGToGotoTransformWF.lean:4340` — `coreCFGToGotoTransform_wellFormed_nonempty`
(round 4 form). The strengthened theorem at line 6883 supersedes it
and is the only consumer in active code (every `_v2/_v3/_v4/_v5`
calls `_strengthened`). `_nonempty` is referenced only in `_strengthened`'s
body (line 6943: `exact coreCFGToGotoTransform_wellFormed_nonempty …`)
as a delegated implementation.

The "outer" `coreCFGToGotoTransform_wellFormed` theorem at line
5376 turned out to be **inside a markdown documentation block**
(lines 5363-5417 are wrapped in `/-! ... ```lean ... ``` ... -/`),
not live code — so the `admit` placeholder in its body is harmless.
Acknowledged in the surrounding prose. **Not removable**;
the round-2 sketch is documentation. Worth a note that the
tristate `_/_nonempty/_strengthened` naming is confusing and one of
the two live names could probably be renamed in a follow-up
("the round-4 nonempty form is the loop-induction proof, the
strengthened form just adds A4 hypothesis closures on top").

(Skimmed; recommendations based on grep + docstring context, not a
full read of the 6918-LoC `CoreCFGToGotoTransformWF.lean`.)

### 2. Duplication

#### 2.1 Parallel "preserves predicate" skeletons in `NoDead.lean` and `GotoTargetProvenance.lean`

These two files both prove "this property of the translator state is
preserved by every translator step." Each defines a property
(`HasNoDead` / `NoGotoHasTarget`), then ports it through a chain of
14+ preservation lemmas with identical structure:

| Step | NoDead lemma | GotoTargetProvenance lemma |
|---|---|---|
| 1 | `push_preserves_no_dead` (line 94) | `push_preserves_no_goto_target` (line 86) |
| 2 | `append_two_preserves_no_dead` (122) | `append_two_preserves_no_goto_target` (115) |
| 3 | `toGotoInstructions_preserves_no_dead` (163) | `toGotoInstructions_preserves_no_goto_target` (157) |
| 4 | `coreCFGToGotoCmdStep_preserves_no_dead` (266) | `coreCFGToGotoCmdStep_preserves_no_goto_target` (253) |
| 5 | `cmdsFoldlM_preserves_no_dead` (322) | `cmdsFoldlM_preserves_no_goto_target` (302) |
| 6 | `emitLabel_preserves_no_dead` (349) | `emitLabel_preserves_no_goto_target` (332) |
| 7 | `emitCondGoto_preserves_no_dead` (367) | `emitCondGoto_preserves_no_goto_target` (349) |
| 8 | `emitUncondGoto_preserves_no_dead` (383) | `emitUncondGoto_preserves_no_goto_target` (363) |
| 9 | `endFunction_emit_preserves_no_dead` (399) | `endFunction_emit_preserves_no_goto_target` (377) |
| 10 | `coreCFGToGotoBlockStep_preserves_no_dead` (420) | `coreCFGToGotoBlockStep_preserves_no_goto_target` (396) |
| 11 | `blocksFoldlM_preserves_no_dead` (488) | `blocksFoldlM_preserves_no_goto_target` (458) |
| 12 | `coreCFGToGotoPatchStep_preserves_no_dead_no_contracts` (520) | `coreCFGToGotoPatchStep_preserves_no_goto_target_no_contracts` (489) |
| 13 | `patchesFoldlM_preserves_no_dead_no_contracts` (530) | `patchesFoldlM_preserves_no_goto_target_no_contracts` (499) |
| 14 | `patchGotoTargets_preserves_no_dead` (547) | (no analogue — see below) |

The proofs are byte-for-byte parallel except for the conjunction
shape of the predicate body (`P(instr)` for `NoDead`, `P(instr) →
target = none` for `GotoTargetProvenance`).

**Proposed unification.** A generic combinator like

```lean
def InstrPredicate := Instruction → Prop

structure InstrPredicateClosed (P : InstrPredicate) where
  closed_under_emit_label    : ...
  closed_under_emit_condGoto : ...
  closed_under_emit_uncondGoto : ...
  closed_under_endFunction   : ...
  closed_under_dec_assn      : ... -- non-DEAD non-GOTO instrs
  closed_under_function_call : ...

theorem translator_preserves_predicate
    (P : InstrPredicate) (h : InstrPredicateClosed P)
    (... translator hypotheses ...) :
    ∀ pc instr, ans.instructions[pc]? = some instr → P instr
```

with the per-step `_preserves_*` lemmas reduced to per-emit-helper
side conditions on `P` (a few lines each), should compress steps
3-13 of both files into a single shared chain of ~250-300 LoC plus
two ~40-LoC instances of the side conditions.

Estimated saving: **~600-800 LoC** across the two files (NoDead
716 LoC → ~250 LoC; GotoTargetProvenance "predicate-preservation"
fragment 90-490 LoC → ~150 LoC; the patcher-specific reverse-target
stuff in GotoTargetProvenance:520-1116 stays as-is).

Risk: the GotoTargetProvenance file additionally has a
`patchGotoTargets`-specific lemma (`patchGotoTargets_target_some_in_patches`
at line 704) that uses the predicate's specific shape (`target = none →
target = some t → membership in patches`). This tail of the file
(~600 LoC) is genuinely specific; the unification only helps the
preservation skeleton.

#### 2.2 Patcher lemmas duplicated between `CoreCFGToGotoTransformWF.lean` and `GotoTargetProvenance.lean`

`CoreCFGToGotoTransformWF.lean:5453-5582` defines five `private theorem`s:

* `patch_one_target_eq` (5453)
* `patch_one_target` (5465)
* `patch_one_preserves_size` (5474)
* `patch_foldl_preserves_size` (5480)
* `patch_one_other_index` (5494)
* `patch_foldl_target_preserved_when_idx_unique_in_tail` (5507)
* `patch_foldl_target_head` (5534)
* `patch_foldl_target_at_idx_when_last` (5555)

`GotoTargetProvenance.lean:523-661` defines a near-byte-identical
parallel set:

* `patch_one_other_index` (523) — verbatim from WF:5494
* `patch_one_target_local` (534) — same as WF's `patch_one_target` modulo name
* `patch_foldl_preserves_size_local` (548) — same as WF's `patch_foldl_preserves_size`
* `patch_foldl_target_preserved_when_idx_unique_in_tail` (583) — verbatim from WF:5507
* `last_occurrence_split` (609) — new in GotoTargetProvenance
* `patch_foldl_target_at_last` (637) — close cousin of WF's `patch_foldl_target_at_idx_when_last`
* `patch_foldl_target_some_in_list` (666) — new in GotoTargetProvenance

The duplication is forced by the WF lemmas being marked `private`,
so the `GotoTargetProvenance` author re-derived them. Promoting the
WF lemmas to public (or moving them into a small shared
`PatcherLemmas.lean`) would eliminate ~140 LoC from
`GotoTargetProvenance.lean`.

(Skimmed both file sections; spot-checked that the lemma statements
are identical modulo renaming.)

#### 2.3 Per-operator skeleton in `ExprTranslationPreservesEvalBoolInt.lean`

13 per-operator lemmas at lines 517-712 each have the shape:

```lean
theorem <opName>_translated
    {δ ...} {δ_goto ...} {δ_goto_bool ...}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"<opString>", ()⟩ ty) e1c) e2c)
      ⟨.<gotoCtor> .<gotoOp>, .<gotoTy>, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.<opName>_corr σ m₁ m₂ ty e1c e2c e1g e2g v)
```

Each lemma is ~12 LoC (with the doc comment); 13 of them = ~156
LoC. They could be reduced to a single ~30-LoC generic over an
operator descriptor (string × goto-constructor × goto-output-type),
or to 13 one-line `simp` proofs delegating to a generic helper that
eats the descriptor.

The same skeleton repeats in the **bridge helpers** at lines
1111-1962 (private `isBoolIntTranslated_of_toGotoExprCtx_*`
theorems). Each bridge helper is ~60-80 LoC and there are 13 of
them, ~900 LoC of essentially identical body modulo the operator
name string and a single constructor name. A tactic-wrapper
(`bridge_op_tac` invoked with `(opName := "Int.Add", redField :=
.intAdd, signedField := .isSignedBvOp_intAdd, ctor := .intAdd)`)
could reduce each to 5-10 LoC.

**Estimated saving: ~600-800 LoC** if the per-operator + per-bridge
duplication is collapsed into two generics. Caveat: the 13
constructors of `IsBoolIntTranslated` (lines 759-893) cannot be
collapsed similarly without losing the "one inductive case per
operator" interface — but their statements are short enough to be a
non-issue.

(Skimmed; the structural similarity is unmistakable from the
operator-by-operator blocks but I have not checked whether
auto-derivation hits edge cases.)

#### 2.4 `Option.some.inj (h_at.symm.trans h_decl_at)` boilerplate in `CmdProvenance.lean`

`grep -c "Option.some.inj" CmdProvenance.lean` returns **11
occurrences** in 372 LoC. Each occurrence is part of the same
3-line idiom:

```lean
have h_eq : instr = i_<emit> :=
  Option.some.inj (h_at.symm.trans h_<emit>_at)
subst h_eq
```

Across the three top-level theorems
(`decl_provenance_of_translator`, `assn_provenance_of_translator`,
`assn_nondet_provenance_of_translator_strict`), this idiom recurs
once per `CmdEmittedAt` constructor case-split. With 7
`CmdEmittedAt` constructors, the three theorems should have
3 × 7 = 21 occurrences — but several are absorbed because
some theorems only need a subset of constructors (the DECL theorem
contradicts at the ASSIGN cases, etc.).

A small `tactic` macro `inj_subst h_at h_emit_at` could collapse
each occurrence to one line. Estimated saving: **~30-50 LoC** in
`CmdProvenance.lean`. Modest, but the readability win is large
(every `cases h_emit with` block then has 3-5 lines of meaningful
work instead of 9-12 lines of boilerplate plus 3 lines of work).

#### 2.5 Repeated `Cmd_toGotoInstructions_<X>_ok` shape in `CoreCFGToGotoTransformWF.lean`

Six `_ok` theorems at lines 88, 144, 182, 224, 257, 871, each
proving "the per-Cmd translator emit returns an `.ok` value with a
specific layout shape". The shape pattern (named `_gty`, `_e_goto`,
`_i_decl`, `_i_assn`, etc., and a long conjunction) is identical
modulo number of conjuncts. The `_set_nondet_ok` (line 871) is
located far from its siblings — likely added in a later round
without merging back.

(Not investigated deeply; called out for awareness only — the body
of each is mostly `unfold` + `simp` so refactoring may not save
much without a tactic that synthesises the conjunction shape.)

### 3. Shrinkability via abstraction

#### 3.1 Generic predicate-preservation combinator (see also §2.1)

A single abstract theorem stating "if a `Prop`-valued predicate `P :
Instruction → Prop` is preserved by every translator emit step,
then it holds of every instruction in `coreCFGToGotoTransform`'s
output" would replace ~14 NoDead lemmas + ~14 GotoTargetProvenance
lemmas with ~5 generic ones. **~600-800 LoC** estimated saving.

The abstraction also generalises to *any* future predicate (e.g.,
"every LOCATION instruction has a unique label", "every ASSIGN
instruction's lhs is a `.symbol` constructor"). It would amortise
the next "preserves" lemma over future audits.

#### 3.2 Single `CmdEmitsLhs` field on the four lhs-shaped `CmdEmittedAt` constructors

`CoreCFGToGOTOInvariants.lean:162-228` has four constructors
(`init_det`, `init_nondet`, `set_det`, `set_nondet`) sharing a
common shape:

* `pgm.instrAt pc = some i_decl/i_assn`
* `i_<x>.type = .DECL/.ASSIGN`
* `i_<x>.code = Code.<decl|assign> (Expr.symbol (identToString v) gty) [e_goto]`

A single private record field `CmdEmitsLhs` capturing
"`<at>`/`<ty>`/`<code>` form the standard symbol-shape" could be
shared across all four constructors:

```lean
structure CmdEmitsLhs (pgm : Program) (pc : Nat) (instr_ty : InstructionType)
    (v : Core.Expression.Ident) (gty : CProverGOTO.Ty)
    (rhs : Code) where
  at  : pgm.instrAt pc = some <(instr_ty, sym v gty, rhs)-shaped>
  ty  : <instr's type = instr_ty>
  ...
```

If structurally adopted, each `CmdEmittedAt` constructor's
hypothesis count drops from 8-12 to 3-4. Downstream theorems that
currently `cases h_emit` on the seven constructors then re-derive
`Option.some.inj (h_at.symm.trans h_<emit>_at)` (see §2.4) would
get the equality "for free" via record projection.

Estimated saving in `CoreCFGToGOTOInvariants.lean` itself: **~30
LoC** (the four constructors compress). Estimated saving in
downstream consumers (`CmdProvenance.lean`, `WellFormedTranslationProps.lean`,
`InstructionLookups.lean`, `CoreCFGToGotoTransformWF.lean`'s
`cmdEmittedAt_*_of_toGotoInstructions` lemmas): **~50-100 LoC**
of `Option.some.inj`/`subst h_eq`/`rw [h_<x>_ty] at h_ty` patterns
that disappear.

Risk: changing `CmdEmittedAt`'s constructor shape is a load-bearing
change touching most of the proof. Should be done in coordination
with a planned round; not a free-lunch refactor.

#### 3.3 Operator descriptor `OpDesc` for `BoolIntOpHypotheses` and per-operator lemmas

The `BoolIntOpHypotheses` structure
(`ExprTranslationPreservesEvalBoolInt.lean:145-326`) has 23 fields,
each parameterised by:

* a Core operator name string (`"Int.Add"`, etc.),
* a GOTO `Expr.Identifier` (`.multiary .Plus`, etc.),
* a GOTO output type (`.Integer`/`.Boolean`),
* arity (1/2/3, including the `.eq`/`.ite` shapes),
* a "boolean view" companion field for booleans.

A single `OpDesc` record plus a function `BoolIntOpAgreesAt
(δ, δ_goto, δ_goto_bool) (op : OpDesc) : Prop` could collapse the
23 fields into a single function-valued field
`agrees_at : ∀ op ∈ supportedOps, BoolIntOpAgreesAt _ _ _ op`.

If adopted, the per-operator lemmas at lines 517-712 collapse to a
single generic helper, and the per-operator bridge helpers at
lines 1111-1962 also collapse via an analogous `OpDescBridges`
record. Estimated saving: **~600-800 LoC** in B3 alone.

Risk: changes the user-facing interface for callers of B3 (the
`BoolIntOpHypotheses` structure shape). Discoverable callers in
`CoreCFGToGOTOConcrete.lean` (only `_v3/_v4/_v5`'s `h_op` parameter
references it), so the blast radius is small.

#### 3.4 Single LiftThroughFold combinator

The `cmdsFoldlM_preserves_no_dead` / `blocksFoldlM_preserves_no_dead`
/ `patchesFoldlM_preserves_no_dead` pattern of "lift a per-step
preservation lemma through `foldlM`" is repeated across three
files:

* `NoDead.lean` (3 instances)
* `GotoTargetProvenance.lean` (3 instances)
* `CoreCFGToGotoTransformWF.lean` (more — `*FoldlM_preserves_size_eq`,
  `*FoldlM_preserves_locationNum_eq_index`, `*FoldlM_layout_block_body`,
  etc.)

A generic
```lean
theorem foldlM_preserves
    (f : β → α → Except ε β) (P : β → Prop)
    (h : ∀ b a b', f b a = .ok b' → P b → P b')
    (xs : List α) (b₀ b' : β)
    (h_run : xs.foldlM f b₀ = .ok b') (h_init : P b₀) : P b'
```

would supersede all of them. Each per-step `*_preserves_*` then
reduces from ~25 LoC of induction to a 2-3 line `apply foldlM_preserves`.
Estimated saving: **~150-300 LoC** across the three files.

(The Lean 4 standard library presumably has something like this;
the files don't seem to use it.)

### 4. Documentation duplication

The "Tier 2 (Good)" / "Tier 3 (Acceptable)" / "round-X deliverable"
boilerplate appears in many docstring blocks across the worker output
files. Specifically:

* `GotoTargetInRange.lean:34-46` — Tier 2 description.
* `TranslatorBridgeHypsDischarge.lean:24-65, 67-82` — round-6a
  deliverable + boundary-with-later-rounds notes.
* `InstructionLookups.lean:14-80` — round-7c deliverable + strategy.
* `CmdProvenance.lean:13-90` — round-8b deliverable + strategy +
  documenting third-theorem provability.
* `GotoTargetProvenance.lean:15-62` — round-8a deliverable + strategy.
* `NoDead.lean:14-73` — round-7b deliverable + proof structure.
* `ExprTranslationPreservesEvalBoolInt.lean:78-103, 1075-1086, 1947-2028` —
  three doc blocks all explaining the per-operator structure.
* `SteppingBridgesDischarge.lean:13-118` — Worker C's interface.

The "WellFormedTranslation is forward-only; closing the backward
direction requires either …" caveat is repeated almost verbatim in
`GotoTargetInRange.lean:56-74`, `InstructionLookups.lean:36-71` (in
slightly different framing), and `CmdProvenance.lean:36-50`.

A central `docs/CoreToGOTO_ProofPatterns.md` (or sections in the
existing `docs/CoreToGOTO_ProofProgress.md`) covering:

1. The Tier 1/2/3 worker-output classification convention.
2. The "WellFormedTranslation is forward-only" caveat and its three
   workarounds (fields, reverse-mapping lemma, caller obligation).
3. The standard "preservation through translator stages" proof
   skeleton.

would let each worker-output file shrink its docstring to a 5-line
purpose statement plus a link, saving ~50-100 LoC of documentation
across the round-6/7/8 files. Modest impact in raw LoC but a real
clarity win.

### 5. Theorem-version proliferation

This is the most actionable single finding.

The current state:

| Version | Lines | Live caller(s) | Axiom test | Status |
|---|---|---|---|---|
| v1 (unsuffixed) | 102-202 | only `_v2` | no | dead if v2 dies |
| `_v2` | 379-468 | none | no | **dead** |
| `_v3` | 508-723 | none | no | **dead** |
| `_v4` | 761-1010 | only `_v5` | yes | live |
| `_v5` | 1059-1350 | none directly; tested | yes | live |

`_v5` calls `_v4` (line 1337) but **NOT** `_v3` despite the doc
saying "v5 extends v4 which extends v3 which extends v2 which
extends v1". The actual implementation rebuilds WF + bridge from
scratch in `_v3`/`_v4` (each invokes
`coreCFGToGotoTransform_wellFormed_strengthened` and
`steppingBridges_of_translator` directly). Only the `_v2 → v1` and
`_v5 → _v4` deltas are genuine "extends" relations; `_v3` and `_v4`
are stand-alone re-derivations.

**Recommendation.** Delete `_v1`/`_v2`/`_v3` outright. Keep `_v4`
because it's axiom-tested and is a non-trivial waypoint (it
discharges R7c's three lookup fields without R8b's PC inversions
— a different hypothesis surface from `_v5`). Keep `_v5` (the live
top theorem). Add a one-paragraph note in
`docs/CoreToGOTO_ProofProgress.md` recording the historical
derivation order (v1 → v2 → v3 → v4 → v5) as git-archaeology.

Estimated saving: **~440 LoC** in `CoreCFGToGOTOConcrete.lean`
(file shrinks from 1351 to ~910). Plus follow-on savings:

* `wellFormedTranslation_to_translatorBridgeHyps` (bridge v1)
  becomes a one-line delegate to bridge_v2 — could be inlined.
  Saves ~50 LoC in `TranslatorBridgeHypsDischarge.lean`.
* The `ConcreteExprCorr` namespace (B3 → ExprTranslationPreservesEval
  bridge, lines 245-378 of CoreCFGToGOTOConcrete.lean) stays —
  used by `_v4`/`_v5`.

**Hard constraint check.** `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`
covers `_v4` and `_v5` only. Removing `_v1`/`_v2`/`_v3` wouldn't
break the smoke test.

### 6. Tactic-level shrinks

#### 6.1 `inj_subst` macro for `CmdProvenance.lean`'s 11 occurrences

Replace
```lean
have h_eq : instr = i_<x> :=
  Option.some.inj (h_at.symm.trans h_<x>_at)
subst h_eq
```
with `inj_subst h_at h_<x>_at`. **~30 LoC** saved in `CmdProvenance.lean`.

#### 6.2 `case_contra_on_type` macro for impossible-type cases

In `CmdProvenance.lean` and `CoreCFGToGotoTransformWF.lean`'s
`cmdEmittedAt_*` consumer code, the pattern
```lean
| set_det _ _ _ i_assn h_assn_at h_assn_ty _ _ _ _ =>
  have h_eq : instr = i_assn :=
    Option.some.inj (h_at.symm.trans h_assn_at)
  subst h_eq
  rw [h_assn_ty] at h_ty
  cases h_ty
```
appears 8+ times. A `case_contra_on_type h_at h_<x>_at h_<x>_ty
h_ty` macro reduces it to one line. Saves **~50-80 LoC** across
the affected files.

#### 6.3 Generic `cases inner` enumerator for `CmdEmittedAt` consumers

The `cases h_emit with | init_det v _ty _e_core _md i_decl _i_assn
h_decl_at _h_decl_ty ... | init_nondet v _ty _md i_decl ... | ...`
pattern enumerates 7 constructors with mostly-underscored
parameters. A `cases h_emit using CmdEmittedAt.casesOnLhsAt` view
(taking only `at`/`ty`/`code` and the lhs symbol) would compress
each case-block from 5-6 lines to 1-2 lines. Saves **~40-60 LoC**
in `CmdProvenance.lean` and `WellFormedTranslationProps.lean`.

#### 6.4 `omega` instead of explicit `Nat.le_of_not_lt h` chains

Spot-checked `NoDead.lean`'s `push_preserves_no_dead`
(lines 94-119): the proof has explicit `Nat.le_of_not_lt`,
manual `by omega` invocations interleaved with `Array.size_push`
rewrites, and a final `exact absurd h (by simp)`. A single
`omega` after the `by_cases` splits would do most of the bound
arithmetic. Saves **~5-10 LoC per `_preserves_*` lemma**, ~150 LoC
across NoDead and GotoTargetProvenance.

#### 6.5 `decide` instead of explicit `cases h_eq` for `InstructionType` inequalities

Pattern in `NoDead.lean`:
```lean
have h_decl_nd : i_decl.type ≠ .DEAD := by rw [h_decl_ty]; decide
```
already uses `decide`. But many manual `cases h_eq` blocks for
`InstructionType.LOCATION ≠ .GOTO` (e.g., `GotoTargetProvenance.lean:344-345`)
could be `by rw [h_eq]; decide` instead of `cases this`. Modest
gain, **~10-20 LoC**.

## Estimated LoC reduction

Per category, *not assuming abstract refactors*:

| Category | LoC saved | Notes |
|---|---|---|
| 1. Dead code (`_v1`/`_v2`/`_v3`, dead bridge, dead wf-form, unused `_h_inj`s) | **~510** | Direct deletions. Safest. |
| 2. Patcher-lemma duplication (`GotoTargetProvenance` ↔ `WF`) | **~140** | Promote private → public in WF. |
| 6. Tactic-level macros (`inj_subst`, `case_contra_on_type`, `omega` everywhere) | **~250** | Ergonomic; each ~10 lines × ~25 sites. |
| **Subtotal: low-risk** | **~900** | All achievable in a single cleanup PR. |

Per category, *if abstract refactors are landed*:

| Category | LoC saved | Notes |
|---|---|---|
| 2.1/3.1 Generic predicate-preservation combinator (NoDead+GotoTargetProvenance skeleton fusion) | **~700** | Touches two ~700-LoC files. |
| 2.3/3.3 Operator descriptor for B3 (per-operator + per-bridge fusion) | **~700** | Touches ~1500 LoC of B3. |
| 3.2 `CmdEmitsLhs` field unification on `CmdEmittedAt` | **~80-150** | Touches `Invariants` + downstream. |
| 3.4 Single `LiftThroughFold` combinator | **~250** | Touches WF + NoDead + GotoTargetProvenance. |
| 4. Documentation centralisation | **~80** | Modest; mostly clarity. |
| **Subtotal: medium-risk refactors** | **~1700-2000** | Each item is a single coherent PR. |

**Total potential reduction: ~2,500-3,500 LoC** out of ~17,990 LoC
of correctness infrastructure (~14-19% of the proof code).

The **~510 LoC of pure dead-code deletions** is the safest first
step — no proof changes, no abstraction redesign, just removing
unreferenced theorems.

## Risks of acting on this

* **Losing useful waypoints.** `_v2`/`_v3` are pedagogically
  useful even if not consumed. The "this is what closing
  `h_brHyps` bought us" narrative is more legible with the
  intermediate forms intact. Mitigate by recording the historical
  v1→v5 chain in `docs/CoreToGOTO_ProofProgress.md` before
  deletion (so git-archaeology stays cheap). Risk grade: low.
* **Breaking the axiom-test set.** `CoreCFGToGOTOConcreteAxioms.lean`
  references `_v4` and `_v5` (which stay). `GotoTargetProvenanceAxioms.lean`
  references both `_of_translator` and `_of_translator_translatorMap`
  (the wf-form is what's flagged for deletion in §1.3). Mitigation:
  delete the corresponding axiom-test entry. Risk grade: low.
* **Breaking the documented historical narrative.**
  `docs/CoreToGOTO_ProofStatusRound8.md`, `docs/CoreToGOTO_CurrentStatus.md`,
  and the per-round supervisor reports refer to `_v1`-`_v5` by
  name. Mitigation: note in the docs that `_v2`/`_v3` were
  removed as historical waypoints; the doc tables can stay if
  marked "(removed in cleanup round)". Risk grade: low-medium.
* **Generic combinators may not abstract cleanly.** Lean 4's
  module system + universe polymorphism + the specific shape of
  `Imperative.GotoTransform` + the inductive `CmdEmittedAt`
  carrying type-equality witnesses — any of these could make a
  "clean" generic combinator unwieldy in practice. The
  `LiftThroughFold` and `InstrPredicateClosed` proposals are
  educated guesses; **a prototype attempt is the right way to
  validate them** before committing. Risk grade: medium.
* **Tactic macros may have edge cases.** `inj_subst` and
  `case_contra_on_type` depend on stable hypothesis-naming
  conventions across the proof. Some `Option.some.inj` sites use
  `<at>.symm.trans <other>` and others use `<other>.symm.trans <at>`
  (see `CoreCFGToGotoTransformWF.lean:5340`'s `cmdEmittedAt_set_nondet`
  body for an example). The macro would need flexibility on
  orientation. Risk grade: low-medium.

## Recommended order of attack

If a future round wants to shrink, the recommended order is:

1. **Delete `_v1`/`_v2`/`_v3` of the concrete forward simulation.**
   Single file (`CoreCFGToGOTOConcrete.lean`), no proof-side
   changes, ~440 LoC reduction. Add a paragraph in
   `docs/CoreToGOTO_ProofProgress.md` recording the old derivation
   chain. **Smallest, safest, biggest single saving.**
2. **Delete the unused `_h_inj` parameters in `InstructionLookups.lean`.**
   Three theorems, three call sites in `TranslatorBridgeHypsDischarge.lean`.
   ~15 LoC saved, but a clarity win.
3. **Promote the WF private patcher lemmas.** Move them to a
   small `Strata/Backends/CBMC/GOTO/PatcherLemmas.lean`, drop
   the duplicates in `GotoTargetProvenance.lean`. ~140 LoC saved.
4. **Add `inj_subst` and `case_contra_on_type` tactic macros.**
   Apply across `CmdProvenance.lean` first, then survey
   `CoreCFGToGotoTransformWF.lean`'s `cmdEmittedAt_*_of_toGotoInstructions`
   theorems for further sites. ~80-130 LoC saved.
5. **Centralise the round-by-round/Tier 1-2-3 documentation
   patterns.** ~80 LoC saved.
6. **(Larger refactor.) Generic `InstrPredicateClosed` combinator
   for NoDead+GotoTargetProvenance.** ~600-800 LoC saved.
   Should be its own dedicated PR.
7. **(Larger refactor.) Generic `OpDesc` for B3.** ~600-800 LoC
   saved. Separate PR.

Items 1-5 are independent and could be landed in one cleanup
sprint. Items 6-7 each merit their own multi-day effort and
should be staged so build breakage is localised.

After items 1-5 alone: the round-6/7/8 surface should be ~7,000
LoC down to ~6,200 LoC. After items 1-7: ~7,000 down to ~5,000.
The round-1-5 work in `CoreCFGToGotoTransformWF.lean` is largely
out of scope for this audit (only the patcher-lemmas duplication
in §2.2 is flagged).
