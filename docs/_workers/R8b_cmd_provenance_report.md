# Worker R8b — Cmd provenance theorems

**Round:** 8
**Branch:** worktree off `htd/unstructured-to-goto` (HEAD `e2c552ab6`).
**Goal:** Discharge R7c's three provenance hypotheses
(`h_decl_provenance`, `h_assn_provenance`,
`h_assn_nondet_provenance`) by translator induction, in a new file
`Strata/Backends/CBMC/GOTO/CmdProvenance.lean`.

## Outcome

**Tier-2 (Good)** for the first two hypotheses; **Tier-3 (partial)**
for the third. Specifically:

- `decl_provenance_of_translator` — closed under a single auxiliary
  CFG-PC inversion hypothesis (`DeclPcInversion`).
- `assn_provenance_of_translator` — closed under a single auxiliary
  CFG-PC inversion hypothesis (`AssignPcInversion`).
- `assn_nondet_provenance_of_translator_strict` — closed under a
  *strict* inversion (`AssignNondetPcInversion`) saying every ASSIGN PC
  is a `set _ .nondet _` cmd-start. This inversion is satisfied only
  for source CFGs where no ASSIGN comes from `init_det` or `set_det` —
  a restrictive precondition. The hypothesis as written in the v2
  bridge demands every ASSIGN have a nondet rhs, which is provably
  false for general translator outputs.

`lake build` green at every commit (585 jobs).

Axioms: `[propext, Classical.choice, Quot.sound]` (all three
theorems; same set as `coreCFGToGoto_forward_simulation`).

## Why Tier-2 (not Tier-1)

Tier-1 (closing the inversion from `wf` alone) requires a CFG-PC
inversion lemma — given a `pc` carrying a DECL/ASSIGN instruction,
recover the block `(l, blk) ∈ cfg.blocks` and offset `k` such that the
PC sits at the cmd's emit. This is mechanical from the translator's
outer-loop induction (each emit step preserves a PC-to-block-cmd
map), but the proof is estimated at 100-200 LoC of structural
translator reasoning — out of scope for a single-round Tier-2
deliverable as the supervisor's prompt anticipated.

## Why the third theorem can't be discharged universally

The v2 bridge's `h_assn_nondet_provenance` field is universal over
ASSIGN PCs:

```lean
∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .ASSIGN →
  ∃ v_src gty rhs_emitted,
    instr.code = Code.assign (Expr.symbol (nameMap v_src) gty) rhs_emitted ∧
    rhs_emitted.id = .side_effect .Nondet
```

This claims **every ASSIGN has a nondet rhs**. That is false: the
translator's `Cmd.toGotoInstructions` emits ASSIGN instructions for
both `set _ (.det _) _` (rhs = translated source expression) and
`init _ _ (.det _) _` (same). Their rhs's `id` is the translated
expression's id, not `.side_effect .Nondet`.

`assign_nondet_lookup` in `TranslatorBridgeHyps` is *intended* to fire
only at PCs where a `step_assign_nondet` runtime step occurs — but the
field's signature does not pin this to a per-firing context; it
demands the universal claim. R7c's bridge consumed this as-is to
produce the v2 lemma, but discharging it from `wf` requires either
(a) refactoring the bridge so that `assign_nondet_lookup`'s
provenance/pinning split exposes a per-firing precondition, or
(b) restricting the source CFG to a "nondet-only" fragment (very
strong).

We document the boundary clearly and provide
`assn_nondet_provenance_of_translator_strict` as a working theorem
under the strict inversion. This serves as the
"what-the-translator-can-prove" form; the bridge-level refactor is
the "what-the-consumer-needs" task, deferrable to a follow-up round.

## Files

- **Added** `Strata/Backends/CBMC/GOTO/CmdProvenance.lean`
  (~370 LoC).
- **Added** `docs/_workers/R8b_cmd_provenance_report.md` (this file).

## Theorem signatures

```lean
abbrev DeclPcInversion (cfg pgm δ δ_goto δ_goto_bool wf) : Prop :=
  ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .DECL →
    ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner

theorem decl_provenance_of_translator
    (cfg pgm δ δ_goto δ_goto_bool wf)
    (h_inversion : DeclPcInversion ...) :
    ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .DECL →
      ∃ v_src gty,
        instr.code = Code.decl
          (Expr.symbol (Imperative.ToGoto.identToString v_src) gty)

abbrev AssignPcInversion (cfg pgm δ δ_goto δ_goto_bool wf) : Prop :=
  ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .ASSIGN →
    -- offset-0 (set case)
    (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v cv md)) ∨
    -- offset-1 (init_det case)
    (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
      CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
        (.init v ty (.det e_core) md))

theorem assn_provenance_of_translator
    (cfg pgm δ δ_goto δ_goto_bool wf)
    (h_inversion : AssignPcInversion ...) :
    ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      ∃ v_src gty rhs_emitted,
        instr.code = Code.assign
          (Expr.symbol (Imperative.ToGoto.identToString v_src) gty)
          rhs_emitted

abbrev AssignNondetPcInversion (cfg pgm δ δ_goto δ_goto_bool wf) : Prop :=
  ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .ASSIGN →
    ∃ v md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v .nondet md)

theorem assn_nondet_provenance_of_translator_strict
    (cfg pgm δ δ_goto δ_goto_bool wf)
    (h_inversion : AssignNondetPcInversion ...) :
    ∀ {pc instr}, pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      ∃ v_src gty rhs_emitted,
        instr.code = Code.assign
          (Expr.symbol (Imperative.ToGoto.identToString v_src) gty)
          rhs_emitted ∧
        rhs_emitted.id = .side_effect .Nondet
```

The `wf` parameter is currently bookkeeping (passed for
identification of which inversion goes with which `wf`) but is not
syntactically referenced in the abbrevs' bodies. Closing the inversion
from `wf` alone — the Tier-1 task — would discharge these abbrevs
into definitional consequences of `wf.layout_block_body`.

## Proof skeleton

For each theorem: pull the inversion's `CmdEmittedAt` witness, then
case-split on the constructor:

- **DECL case**: only `init_det` and `init_nondet` admit a DECL at the
  relation-pc; both expose `h_decl_code` directly. The other
  constructors (`set_det`, `set_nondet`, `assert_emit`, `assume_emit`,
  `cover_emit`) all have `instr.type ≠ .DECL` at the relation-pc, so
  the DECL hypothesis contradicts each via `cases h_ty` on the rewritten
  type equality.

- **ASSIGN case (offset-0)**: the inversion gives a `.set v cv md` cmd.
  Sub-case on `cv`: `.det e_core` matches `set_det`; `.nondet` matches
  `set_nondet`. Both expose `h_assn_code` (the latter via the
  existential-witness destructuring).

- **ASSIGN case (offset-1)**: the inversion gives an `.init v ty
  (.det e_core) md` cmd at `pc_pred = pc - 1`, which only matches
  `init_det`. Its `h_assn_code` exposes the symbol shape with the
  ASSIGN at relation-pc + 1 = pc.

- **ASSIGN-Nondet (strict)**: the inversion gives a `.set v .nondet md`
  cmd directly. `set_nondet` matches; the existential rhs has
  `.id = .side_effect .Nondet` by the constructor's witness.

All instruction-equality steps (`instr = i_decl` etc.) come from
`Option.some.inj` on the `instrAt` hypotheses.

## Build verification

```
$ lake build
Build completed successfully (585 jobs).

$ lake env lean tmp/axiom_check.lean
'CProverGOTO.CmdProvenance.decl_provenance_of_translator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.CmdProvenance.assn_provenance_of_translator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.CmdProvenance.assn_nondet_provenance_of_translator_strict'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Next-step suggestions

To raise R8b from Tier-2 to Tier-1, close the inversion abbrevs from
`wf` alone. Concrete plan:

1. **Add a `WellFormedTranslation.pc_to_block_cmd` lemma** (or a
   companion field in `WellFormedTranslation`) that, for every PC
   carrying a body instruction, returns a unique `(l, blk, k, inner)`
   triple such that `(l, blk) ∈ cfg.blocks`, `wf.labelMap l = some
   pc_l`, `pc = pc_l + 1 + cmdsPrefixInstrCount blk.cmds k` (or
   `+ 1` for the second instruction of `init_det`), and `blk.cmds[k]
   = .cmd inner`.

2. **Compose** `pc_to_block_cmd` with `wf.layout_block_body` to get a
   `CmdEmittedAt` witness for any DECL/ASSIGN PC. This discharges
   `DeclPcInversion` and `AssignPcInversion` directly.

3. **For `AssignNondetPcInversion`** — the strict variant — add a
   precondition tying the source-side cmd to `.set _ .nondet _`. This
   is consumer-side (the bisim user knows the source-cmd's shape from
   their EvalCmd hypothesis), not translator-side.

The mechanical inversion (steps 1+2) is the bulk of the remaining
translator-side work for the v2 bridge. After that, only the trace-level
pinning hypotheses (`h_decl_x_pinned`, etc.) remain, and those are
genuinely caller-side (bisim invariants).

## Status checklist

- [x] Verify branch base (`e2c552ab6`).
- [x] Write report stub (`docs/_workers/R8b_cmd_provenance_report.md`).
- [x] Read R7c's lookup-fields report and `InstructionLookups.lean`.
- [x] Read strengthened `CmdEmittedAt` in
      `CoreCFGToGOTOInvariants.lean`.
- [x] Read v2 bridge in `TranslatorBridgeHypsDischarge.lean` for exact
      hypothesis shapes.
- [x] Add `Strata/Backends/CBMC/GOTO/CmdProvenance.lean` with three
      theorems under PC inversion hypotheses.
- [x] Verify `lake build` is green at every commit.
- [x] Verify axiom set unchanged ([propext, Classical.choice,
      Quot.sound]).
- [x] Document the third theorem's "harder" status and propose
      bridge-level refactors to close it.
- [x] Final report.
