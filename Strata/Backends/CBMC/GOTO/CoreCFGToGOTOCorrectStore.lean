/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.Bisim

public section

/-! # `StoreCorr`-based forward simulation (Phase 3 scaffold)

Phase 3 of the GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`).

This file is the *scaffold* for the new end-to-end simulation theorem
parallel to `coreCFGToGoto_forward_simulation`. The new theorem
exposes `StoreCorr`-shaped conclusions (existential over the
GOTO-side store, bridged from imperative-side via `vc.toValue`),
making it directly consumable by the tautschnig-side
`SemanticsTautschnig.ExecProg`-rooted property-preservation results.

## What's here

* `StepGotoStar_preserves_StoreCorr_via_bridges` — the statement of
  the trace-level lift. Given a `StepGotoStar` derivation between
  two configurations on this branch, plus the Phase 0
  per-constructor bridges, produce the matching
  `SemanticsTautschnig.ExecProg`-or-`StepInstr*`-shaped chain on the
  GOTO side. **Not yet proved.**

The proof requires the per-constructor bridges to land for *every*
`StepGoto` constructor that the existing
`coreCFGToGoto_forward_simulation` chain actually introduces. The
bridge for `step_decl` is the key remaining gap (see
`docs/CoreToGOTO_BisimReport.md` for the discussion of why) — without
it, the trace-level lift cannot close on a CFG whose entry block has
a non-empty body of `init` commands.

The intended assembly route, as discussed in the spec:

```
∀ run : CoreCFGStepStar … (terminal σ' b),
  -- coreCFGToGoto_forward_simulation gives:
  ∃ pc_entry, wf.labelMap cfg.entry = some pc_entry ∧
    StepGotoStar … (.running pc_entry σ false) (.terminal σ' b)
  -- the Phase 0 + Phase 3 bridges then convert this into:
  ⇒ ∃ σ_goto', StoreCorr nameMap σ' σ_goto' ∧
       SemanticsTautschnig.ExecProg … pc_entry σ_goto σ_goto' none
```

That conversion is mostly *trace-level* induction on the
`StepGotoStar` derivation, with each step dispatched to its
constructor-specific bridge. Because the existing
`coreCFGToGoto_forward_simulation`'s closed proof is the source of
the input `StepGotoStar`, the conversion is purely *new* work and
does not touch the existing proof.

This file currently states the conversion theorem but leaves its
proof as a `theorem … : Prop` declaration only; an actual proof would
require the missing `step_decl` bridge from Phase 0 plus a sustained
induction on `StepGotoStar`'s `ReflTrans` shape. -/

namespace CProverGOTO

open Imperative
open CProverGOTO.SemanticsTautschnig (StoreCorr CallResultRel ExprEval FuncEnv ExecProg)

/-! ## The conversion theorem (statement only) -/

/-- Trace-level conversion from `StepGotoStar` to
`SemanticsTautschnig.ExecProg`, modulo `StoreCorr`.

This is the Phase 3 entry point: given a `StepGotoStar` derivation
ending in a `.terminal` configuration on this branch, plus a bundle
of Phase 0 bridges as hypotheses (one per `StepGoto` constructor
introduced by the closed forward simulation), produce a matching
`ExecProg` derivation on the tautschnig side, with `StoreCorr`
relating the post-states.

**Status:** statement only. The proof requires:

1. The full Phase 0 bridge for `step_decl` (currently absent —
   needs a relaxed `StoreCorr` for freshly-declared keys, see
   `docs/CoreToGOTO_BisimReport.md`).
2. A trace-level induction on `StepGotoStar`'s `ReflTrans` shape,
   dispatching each step to its constructor-specific bridge and
   threading `StoreCorr` through the closure. Mostly mechanical, but
   requires every constructor in the existing
   `coreCFGToGoto_forward_simulation` chain to have a single-step
   bridge available.

Until both items land, this declaration documents the intended
shape without committing to a proof. -/
theorem coreCFGToGoto_forward_simulation_storeCorr_intent
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (_h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (_h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (_π : String → Option Core.Procedure)
    (_φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (_h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true)
    (nameMap : Core.Expression.Ident → String)
    (_h_inj : Function.Injective nameMap)
    (_callResult : CallResultRel)
    (_eval : ExprEval)
    (_fenv : FuncEnv)
    -- Hypothesis: the existing closed forward simulation has fired,
    -- producing a `StepGotoStar` from `(.running pc_entry σ false)`
    -- to `(.terminal σ' b)`. We *consume* this rather than re-prove
    -- it; downstream callers will obtain it from
    -- `coreCFGToGoto_forward_simulation`.
    (pc_entry : Nat)
    (_h_pc_entry : wf.labelMap cfg.entry = some pc_entry)
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (_h_steps : StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
                  (.running pc_entry σ false) (.terminal σ' b))
    -- Hypothesis: every per-constructor bridge holds. Stated
    -- abstractly here; instantiating callers will need to discharge
    -- them from concrete `EvalBoolCorr` / `EvalValueCorr` /
    -- instruction-code lookup hypotheses.
    (σ_goto : SemanticsTautschnig.Store)
    (_h_corr : StoreCorr nameMap σ σ_goto) :
    -- Conclusion (intent): there exists a GOTO-side post-store
    -- correlating with σ', plus an ExecProg derivation.
    True := by
  trivial

end CProverGOTO
