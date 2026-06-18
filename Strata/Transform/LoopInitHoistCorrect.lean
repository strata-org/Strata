/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.LoopInitHoistContains
public import Strata.Transform.LoopInitHoistFreshness
public import Strata.Transform.LoopInitHoistRewrite
public import Strata.Transform.LoopInitHoistInfra
public import Strata.Transform.DetToKleeneCorrect
public import Strata.Transform.LoopInitHoistLoopDriver
public import Strata.Transform.LoopInitHoistStepCProducer
public import Strata.Transform.LoopInitHoistLoopArmWF
public import Strata.Transform.LoopInitHoistBodyTransport

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra
import all Strata.Transform.LoopInitHoistLoopDriver
import all Strata.Transform.LoopInitHoistStepCProducer
import all Strata.Transform.LoopInitHoistLoopArmWF
import all Strata.Transform.LoopInitHoistBodyTransport

public section

namespace Imperative

/-! # Phase 8 — `Block.hoistLoopPrefixInits` correctness

This module exposes the top-level forward-simulation theorem for the
hoisting pass `Block.hoistLoopPrefixInits` (Strata/Transform/LoopInitHoist.lean):

```
hoistLoopPrefixInits_preserves :
  StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ_src) (.terminal ρ_src') →
  ∃ ρ_h',
    StepStmtStar P (EvalCmd P) extendEval
      (.stmts (Block.hoistLoopPrefixInits ss) ρ_src) (.terminal ρ_h') ∧
    StoreAgreement ρ_src'.store ρ_h'.store ∧
    ρ_h'.hasFailure = ρ_src'.hasFailure
```

The store relation is `StoreAgreement` (semantics preservation *modulo
hoisted variables*), not exact pointwise equality: the hoisting pass lifts
loop-body inits to fresh targets defined only in the hoisted store, so the
hoisted store legitimately carries entries the source store never defines.
`StoreAgreement σ_src σ_h` constrains only source-defined variables, leaving
those fresh hoist targets (and projected loop-locals) correctly unconstrained.

The proof is a mutual structural induction on the source block, dispatching
each `.loop` arm via `loop_preserves_struct` (LoopInitHoistInfra) after
running the hoisted prelude.

## Status

The top-level theorem `hoistLoopPrefixInits_preserves` is fully discharged
(sorry-free).  It is a direct invocation of the §E Block-level mutual
forward-simulation lemma `Block.hoistLoopPrefixInits_preserves`, whose every
arm — `.cmd`, `.block`, `.ite`, `.loop`, `.exit`-free, … — is closed.  The
`.loop` arm runs the hoisted prelude, applies the lift renaming simulation on
the post-order body, and reconciles the loop-entry stores at the union
`HoistInv`.  Phase 10 composition can be wired against the signature directly.
-/

variable {P : PureExpr}

/-! ## §D — Structural preservation re-exports (S2..S5)

Four structural invariants are preserved by `Block.hoistLoopPrefixInits`:

| Invariant | Source | Preservation lemma |
|---|---|---|
| `loopBodyNoInits` | this file | `Block.hoistLoopPrefixInits_satisfies_loopBodyNoInits` |
| `loopHasNoInvariants` | `Stmt.lean` | `Block.hoistLoopPrefixInits_preserves_loopHasNoInvariants` |
| `exitsCoveredByBlocks` | `Stmt.lean` | `Block.hoistLoopPrefixInits_preserves_exitsCoveredByBlocks` |
| `loopMeasureNone` | `LoopInitHoist.lean` (Step 2) | `Block.hoistLoopPrefixInits_preserves_loopMeasureNone` |

S2 (`loopBodyNoInits`) is the postcondition the pass was originally written
for; we re-export the existing public theorem under the canonical Phase 8
naming pattern. S5 (`loopMeasureNone`) was added in Phase 8 §B
(`LoopInitHoist.lean`). S3 and S4 require their own proofs because the pass
only converts `init` to `set` and rewrites loop bodies — neither operation
introduces new loop invariants or new exit statements outside enclosing
blocks. -/

/-- S2 re-export: `Block.hoistLoopPrefixInits` preserves the
`Block.loopBodyNoInits` postcondition (in the trivial sense — the output
*satisfies* it unconditionally).

Phase 8 naming convention: `_preserves_<predicate>` for predicates that
admit a precondition shape; `_satisfies_<predicate>` for postconditions
that hold unconditionally on the pass output. -/
theorem Block.hoistLoopPrefixInits_preserves_loopBodyNoInits
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true :=
  hoistLoopPrefixInits_satisfies_loopBodyNoInits ss

/-! ### S3 — `loopHasNoInvariants` is preserved

The pass never introduces new `.loop` invariants. Each `.loop g m inv body md`
in the input becomes `havocs.map .cmd ++ [.loop g m inv body' md]` where
`havocs` are `.cmd (.init y ty .nondet md)` (no invariants), and `body'` is
the lifted body (which goes through `liftInitsInLoopBody`, which doesn't
recurse into nested `.loop`s and so leaves their invariants untouched).

The value-equation `Block.hoistLoopPrefixInits_loopHasNoInvariants_eq` is
proven (monadic + pure-wrapper bridge) in `LoopInitHoist.lean`; this is the
public preservation re-export under the canonical Phase 8 naming. -/
/-- S3 public preservation entry-point. -/
theorem Block.hoistLoopPrefixInits_preserves_loopHasNoInvariants
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P)))
    (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInits ss) = true := by
  rw [Block.hoistLoopPrefixInits_loopHasNoInvariants_eq]; exact h

/-! ### S4 — `exitsCoveredByBlocks` is preserved

The pass converts `.cmd (.init ...)` to `.cmd (.init ... .nondet)` (no exits)
and rewrites `.loop g m inv body md` to `havocs ++ [.loop g m inv body' md]`,
where the only exits in the output come from the body. Per
`Stmt.exitsCoveredByBlocks`'s `.loop` arm, exits in `body` are checked
against `labels` directly (no enclosing block label is added by the loop),
and the lifted body is structurally a subset of the original body's
exit-bearing tree (init/set commands have no exits). So the predicate is
preserved (in the strong, predicate-equality sense). -/

section ExitsCovered

private theorem Block.exitsCoveredByBlocks_of_map_cmd
    (labels : List String) (cs : List (Cmd P)) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (cs.map (@Stmt.cmd P (Cmd P))) :=
  all_cmd_exitsCoveredByBlocks labels _
    (fun s hs => by
      simp only [List.mem_map] at hs
      obtain ⟨c, _, hc⟩ := hs
      exact ⟨c, hc.symm⟩)

/-! `Block.substIdent` / `Block.applyRenames` rename identifiers only; they
never touch block labels or exit statements, so `exitsCoveredByBlocks` is
invariant under them. (Prop-valued analogue of the Bool walkers'
`SubstIdentPreserves` in `LoopInitHoist.lean`.) -/

mutual
private theorem Stmt.substIdent_exitsCoveredByBlocks [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (y y' : P.Ident) (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Stmt.exitsCoveredByBlocks labels (Stmt.substIdent y y' s) := by
  cases s with
  | cmd c => simp only [Stmt.substIdent_cmd, Stmt.exitsCoveredByBlocks]
  | block lbl bss md =>
    simp only [Stmt.substIdent_block]
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (lbl :: labels)
      (Block.substIdent y y' bss)
    exact Block.substIdent_exitsCoveredByBlocks y y' (lbl :: labels) bss h
  | ite g tss ess md =>
    simp only [Stmt.substIdent_ite]
    exact ⟨Block.substIdent_exitsCoveredByBlocks y y' labels tss h.1,
           Block.substIdent_exitsCoveredByBlocks y y' labels ess h.2⟩
  | loop g m inv body md =>
    simp only [Stmt.substIdent_loop]
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.substIdent y y' body)
    exact Block.substIdent_exitsCoveredByBlocks y y' labels body h
  | exit lbl md => simpa only [Stmt.substIdent_exit, Stmt.exitsCoveredByBlocks] using h
  | funcDecl d md => simp only [Stmt.substIdent_funcDecl, Stmt.exitsCoveredByBlocks]
  | typeDecl t md => simp only [Stmt.substIdent_typeDecl, Stmt.exitsCoveredByBlocks]
  termination_by sizeOf s

private theorem Block.substIdent_exitsCoveredByBlocks [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (y y' : P.Ident) (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.substIdent y y' ss) := by
  match ss with
  | [] => simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  | s :: rest =>
    simp only [Block.substIdent_cons]
    exact ⟨Stmt.substIdent_exitsCoveredByBlocks y y' labels s h.1,
           Block.substIdent_exitsCoveredByBlocks y y' labels rest h.2⟩
  termination_by sizeOf ss
end

private theorem Block.applyRenames_exitsCoveredByBlocks [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (labels : List String)
    (ss : List (Stmt P (Cmd P)))
    (h : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.applyRenames renames ss) := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simpa using h
  | cons p rest ih =>
    simp only [List.foldl_cons]
    exact ih (Block.substIdent p.1 p.2 ss)
      (Block.substIdent_exitsCoveredByBlocks p.1 p.2 labels ss h)

/-! ### Lift residual preserves `exitsCoveredByBlocks`

The `.snd` residual of the monadic lift is unfolded via the `@[simp]`
`Stmt.liftInitsInLoopBody_snd_*` / `Block.liftInitsInLoopBody_snd_*` residual
equations (LoopInitHoist.lean) — the old `simp [Stmt.liftInitsInLoopBody]`
unfold no longer fires under the monadic wrapper. -/

mutual
/-- `Stmt.liftInitsInLoopBody`'s residual block preserves
`Stmt.exitsCoveredByBlocks`. -/
private theorem Stmt.liftInitsInLoopBody_snd_exitsCoveredByBlocks [HasIdent P]
    (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Stmt.liftInitsInLoopBody s).snd := by
  cases s with
  | cmd c =>
    cases c with
    | init x ty rhs md =>
      simp [Stmt.liftInitsInLoopBody_snd_cmd_init, Stmt.exitsCoveredByBlocks,
            Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | set _ _ _ =>
      simp [Stmt.liftInitsInLoopBody_snd_cmd_set, Stmt.exitsCoveredByBlocks,
            Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | assert _ _ _ =>
      simp [Stmt.liftInitsInLoopBody_snd_cmd_assert, Stmt.exitsCoveredByBlocks,
            Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | assume _ _ _ =>
      simp [Stmt.liftInitsInLoopBody_snd_cmd_assume, Stmt.exitsCoveredByBlocks,
            Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | cover _ _ _ =>
      simp [Stmt.liftInitsInLoopBody_snd_cmd_cover, Stmt.exitsCoveredByBlocks,
            Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  | block lbl bss md =>
    simp only [Stmt.liftInitsInLoopBody_snd_block]
    refine ⟨?_, trivial⟩
    show Stmt.exitsCoveredByBlocks labels
      (Stmt.block lbl (Block.liftInitsInLoopBody bss).snd md)
    have h_inner : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (lbl :: labels) bss := h
    exact Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks (lbl :: labels) bss h_inner
  | ite g tss ess md =>
    simp only [Stmt.liftInitsInLoopBody_snd_ite]
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · exact Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks labels tss h.1
    · exact Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks labels ess h.2
  | loop g m inv body md =>
    -- liftInitsInLoopBody does NOT recurse into .loop bodies; output is
    -- `[.loop g m inv body md]` unchanged.
    simp only [Stmt.liftInitsInLoopBody_snd_loop,
               Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    exact ⟨h, trivial⟩
  | exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody_snd_exit,
               Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    exact ⟨h, trivial⟩
  | funcDecl d md =>
    simp [Stmt.liftInitsInLoopBody_snd_funcDecl, Stmt.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  | typeDecl t md =>
    simp [Stmt.liftInitsInLoopBody_snd_typeDecl, Stmt.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  termination_by sizeOf s

/-- `Block.liftInitsInLoopBody`'s residual block preserves
`Block.exitsCoveredByBlocks`. -/
private theorem Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks [HasIdent P]
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.liftInitsInLoopBody ss).snd := by
  match ss with
  | [] =>
    simp [Block.liftInitsInLoopBody_snd_nil,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  | s :: rest =>
    simp only [Block.liftInitsInLoopBody_snd_cons]
    apply block_exitsCoveredByBlocks_append
    · exact Stmt.liftInitsInLoopBody_snd_exitsCoveredByBlocks labels s h.1
    · exact Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks labels rest h.2
  termination_by sizeOf ss
end

/-! ### Hoist pass (monadic) preserves `exitsCoveredByBlocks`

Proven against the monadic pass shape via the `hoistLoopPrefixInitsM_*_out`
residual equations (LoopInitHoist.lean), then bridged to the pure wrapper. The
`.loop` arm's output wraps the lift residual in `Block.applyRenames`, handled
by `Block.applyRenames_exitsCoveredByBlocks`. -/

mutual
/-- `Stmt.hoistLoopPrefixInitsM`'s output preserves `Stmt.exitsCoveredByBlocks`. -/
private theorem Stmt.hoistLoopPrefixInitsM_exitsCoveredByBlocks [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (labels : List String) (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Stmt.hoistLoopPrefixInitsM s σ).1 := by
  match s with
  | .cmd c =>
    simp [Stmt.hoistLoopPrefixInitsM,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks]
  | .block lbl bss md =>
    rw [Stmt.hoistLoopPrefixInitsM_block_out]
    refine ⟨?_, trivial⟩
    show Stmt.exitsCoveredByBlocks labels
      (Stmt.block lbl (Block.hoistLoopPrefixInitsM bss σ).1 md)
    have h_inner : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (lbl :: labels) bss := h
    exact Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks (lbl :: labels) bss σ h_inner
  | .ite g tss ess md =>
    rw [Stmt.hoistLoopPrefixInitsM_ite_out]
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · exact Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels tss σ h.1
    · exact Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels ess _ h.2
  | .loop g m inv body md =>
    rw [Stmt.hoistLoopPrefixInitsM_loop_out]
    -- output: havocs.map .cmd ++ [.loop g m inv (applyRenames renames lifted.snd) md]
    apply block_exitsCoveredByBlocks_append
    · -- prelude havocs: each is .cmd, no exit possible.
      apply Block.exitsCoveredByBlocks_of_map_cmd
    · refine ⟨?_, trivial⟩
      show Stmt.exitsCoveredByBlocks labels
        (Stmt.loop g m inv
          (Block.applyRenames
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) md)
      -- For .loop, exitsCoveredByBlocks unfolds to exitsCoveredByBlocks on body.
      apply Block.applyRenames_exitsCoveredByBlocks
      -- the lift residual `.1.2.2` equals the pure wrapper's `.snd`.
      have h_body : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels body := h
      have h_body_hoisted :
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
            (Block.hoistLoopPrefixInitsM body σ).1 :=
        Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels body σ h_body
      have h_lift :=
        Block.liftInitsInLoopBody_snd_exitsCoveredByBlocks labels
          (Block.hoistLoopPrefixInitsM body σ).1 h_body_hoisted
      rwa [Block.liftInitsInLoopBody,
           Block.liftInitsInLoopBodyM_snd_state_indep
             (Block.hoistLoopPrefixInitsM body σ).1 StringGenState.emp
             (Block.hoistLoopPrefixInitsM body σ).2] at h_lift
  | .exit lbl md =>
    simp [Stmt.hoistLoopPrefixInitsM,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks]
    exact h
  | .funcDecl d md =>
    simp [Stmt.hoistLoopPrefixInitsM,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks]
  | .typeDecl t md =>
    simp [Stmt.hoistLoopPrefixInitsM,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks,
          Stmt.exitsCoveredByBlocks]
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInitsM`'s output preserves `Block.exitsCoveredByBlocks`. -/
private theorem Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (labels : List String) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.hoistLoopPrefixInitsM ss σ).1 := by
  match ss with
  | [] =>
    simp [Block.hoistLoopPrefixInitsM,
          Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
  | s :: rest =>
    rw [Block.hoistLoopPrefixInitsM_cons_out]
    apply block_exitsCoveredByBlocks_append
    · exact Stmt.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels s σ h.1
    · exact Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels rest _ h.2
  termination_by sizeOf ss
end

/-- S4 public preservation entry-point (pure-wrapper bridge). -/
theorem Block.hoistLoopPrefixInits_preserves_exitsCoveredByBlocks [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels
      (Block.hoistLoopPrefixInits ss) := by
  rw [Block.hoistLoopPrefixInits]
  exact Block.hoistLoopPrefixInitsM_exitsCoveredByBlocks labels ss StringGenState.emp h

end ExitsCovered

/-! ### S5 — `loopMeasureNone` re-export

Already proven in `LoopInitHoist.lean` (Phase 8 §B). Re-exported here for
symmetry under the canonical Phase 8 naming. -/

theorem Block.hoistLoopPrefixInits_preserves_loopMeasureNone'
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P)))
    (h : Block.loopMeasureNone ss = true) :
    Block.loopMeasureNone (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInits_preserves_loopMeasureNone ss h

/-! ### §E undefinedness-frame helper infra

Supporting lemmas for the `cons` arm of the §E Block sibling: the tail IH's
`h_hoist_undef` precondition (every `y ∈ Block.initVars rest` is undefined in
the *mid* source store) is re-established by transporting `store y = none`
across the terminating head run.  This needs a config-level undefinedness
invariant `NoneAtY` preserved along the step relation, plus the bridge between
`containsFuncDecl = false` (the §E shape precondition) and the `definedVars =
initVars` / `noFuncDecl` facts the transport consumes. -/

/-- `UpdateState` preserves undefinedness: if `σ y = none`, then `σ' y = none`
(the target was already defined, so `y` cannot be the target). -/
private theorem UpdateState_preserves_none
    {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h_us : UpdateState P σ x v σ') (h_none : σ y = none) :
    σ' y = none := by
  cases h_us with
  | update h_was _ h_other =>
    by_cases hxy : x = y
    · subst hxy; rw [h_none] at h_was; exact absurd h_was (by simp)
    · rw [h_other y hxy]; exact h_none

/-- `InitState` preserves the slot of any `y ≠` the init target. -/
private theorem InitState_preserves_none
    {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h_is : InitState P σ x v σ') (h_ne : x ≠ y) :
    σ' y = σ y := by
  cases h_is with
  | init _ _ h_other => exact h_other y h_ne

-- Under no funcDecls, a statement's `definedVars` (init + funcname targets)
-- coincides with its `initVars` (init targets only): the only divergence is the
-- `.funcDecl` arm, excluded by `containsFuncDecl = false`.
mutual
private theorem Stmt.definedVars_eq_initVars_of_no_fd
    (s : Stmt P (Cmd P)) (h : Stmt.containsFuncDecl s = false) :
    Stmt.definedVars (P := P) (C := Cmd P) s = Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp only [Stmt.definedVars, Stmt.initVars, Cmd.definedVars,
                   HasVarsImp.definedVars]
  | .block lbl bss md =>
      rw [Stmt.definedVars, Stmt.initVars, Stmt.containsFuncDecl] at *
      exact Block.definedVars_eq_initVars_of_no_fd bss h
  | .ite g tss ess md =>
      rw [Stmt.definedVars, Stmt.initVars, Stmt.containsFuncDecl, Bool.or_eq_false_iff] at *
      rw [Block.definedVars_eq_initVars_of_no_fd tss h.1,
          Block.definedVars_eq_initVars_of_no_fd ess h.2]
  | .loop g m inv body md =>
      rw [Stmt.definedVars, Stmt.initVars, Stmt.containsFuncDecl] at *
      exact Block.definedVars_eq_initVars_of_no_fd body h
  | .exit lbl md => simp [Stmt.definedVars, Stmt.initVars]
  | .funcDecl d md => rw [Stmt.containsFuncDecl] at h; exact absurd h (by simp)
  | .typeDecl t md => simp [Stmt.definedVars, Stmt.initVars]
  termination_by sizeOf s

private theorem Block.definedVars_eq_initVars_of_no_fd
    (ss : List (Stmt P (Cmd P))) (h : Block.containsFuncDecl ss = false) :
    Block.definedVars (P := P) (C := Cmd P) ss = Block.initVars ss := by
  match ss with
  | [] => simp [Block.definedVars, Block.initVars]
  | s :: rest =>
      rw [Block.definedVars, Block.initVars, Block.containsFuncDecl, Bool.or_eq_false_iff] at *
      rw [Stmt.definedVars_eq_initVars_of_no_fd s h.1,
          Block.definedVars_eq_initVars_of_no_fd rest h.2]
  termination_by sizeOf ss
end

/-- If `y ∉ Block.definedVars ss`, then `y ∉ Stmt.definedVars s` for `s ∈ ss`. -/
private theorem all_not_mem_definedVars_of_block
    {y : P.Ident} {ss : List (Stmt P (Cmd P))}
    (h : y ∉ Block.definedVars (P := P) (C := Cmd P) ss) :
    ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s := by
  induction ss with
  | nil => intro s hs; exact absurd hs (List.not_mem_nil)
  | cons s rest ih =>
    rw [Block.definedVars] at h
    intro s' hs'
    rcases List.mem_cons.mp hs' with h_eq | h_in
    · exact h_eq ▸ (fun hc => h (List.mem_append.mpr (Or.inl hc)))
    · exact ih (fun hc => h (List.mem_append.mpr (Or.inr hc))) s' h_in

/-- Config-level undefinedness invariant for `y`: every store reachable from
`cfg` maps `y` to `none`, and no pending statement INITs `y` (so the running
trace cannot define it; `set y` cannot fire either, as the target must already
be defined). -/
@[expose] def NoneAtY (y : P.Ident) : Config P (Cmd P) → Prop
  | .stmt s ρ => ρ.store y = none ∧ y ∉ Stmt.definedVars (P := P) (C := Cmd P) s
  | .stmts ss ρ => ρ.store y = none ∧ ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s
  | .terminal ρ => ρ.store y = none
  | .exiting _ ρ => ρ.store y = none
  | .block _ σ_parent inner => σ_parent y = none ∧ NoneAtY y inner
  | .seq inner ss => NoneAtY y inner ∧ ∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s

open StructuredToUnstructuredCorrect in
/-- A single command preserves undefinedness of `y` when `y` is not the
command's init/set target. -/
private theorem EvalCmd_preserves_none
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {hf : Bool} {y : P.Ident}
    (h_none : σ y = none)
    (h_not_def : y ∉ Cmd.definedVars c)
    (h_eval : EvalCmd P δ σ c σ' hf) :
    σ' y = none := by
  simp only [Cmd.definedVars] at h_not_def
  cases h_eval with
  | eval_init _ h_is _ _ =>
    rw [InitState_preserves_none h_is (fun h => h_not_def (h ▸ List.mem_singleton.mpr rfl))]
    exact h_none
  | eval_init_unconstrained h_is _ =>
    rw [InitState_preserves_none h_is (fun h => h_not_def (h ▸ List.mem_singleton.mpr rfl))]
    exact h_none
  | eval_set _ h_us _ _ => exact UpdateState_preserves_none h_us h_none
  | eval_set_nondet h_us _ => exact UpdateState_preserves_none h_us h_none
  | eval_assert_pass _ _ _ => exact h_none
  | eval_assert_fail _ _ _ => exact h_none
  | eval_assume _ _ _ => exact h_none
  | eval_cover _ => exact h_none

/-- Single-step preservation of `NoneAtY`. -/
private theorem NoneAtY_step
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {y : P.Ident} {cfg cfg' : Config P (Cmd P)}
    (h_step : StepStmt P (EvalCmd P) extendEval cfg cfg')
    (h_inv : NoneAtY (P := P) y cfg) :
    NoneAtY (P := P) y cfg' := by
  induction h_step with
  | step_cmd h_eval =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    refine EvalCmd_preserves_none h_none ?_ h_eval
    simpa [Stmt.definedVars] using h_ndef
  | step_block =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    exact ⟨h_none, h_none, all_not_mem_definedVars_of_block (by simpa [Stmt.definedVars] using h_ndef)⟩
  | step_ite_true _ _ =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inl hc)))⟩
  | step_ite_false _ _ =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inr hc)))⟩
  | step_ite_nondet_true =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inl hc)))⟩
  | step_ite_nondet_false =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inr hc)))⟩
  | step_loop_enter _ _ _ _ =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    refine ⟨⟨h_none, h_none, all_not_mem_definedVars_of_block h_ndef⟩, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with h_eq | h_in
    · subst h_eq; rw [Stmt.definedVars]; exact h_ndef
    · exact absurd h_in (List.not_mem_nil)
  | step_loop_exit _ _ _ _ =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_loop_nondet_enter _ =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    rw [Stmt.definedVars] at h_ndef
    refine ⟨⟨h_none, h_none, all_not_mem_definedVars_of_block h_ndef⟩, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with h_eq | h_in
    · subst h_eq; rw [Stmt.definedVars]; exact h_ndef
    · exact absurd h_in (List.not_mem_nil)
  | step_loop_nondet_exit _ =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_exit =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_funcDecl =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_typeDecl =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_stmts_nil =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_stmts_cons =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    exact ⟨⟨h_none, h_ndef _ (List.mem_cons_self)⟩,
           fun s' hs' => h_ndef s' (List.mem_cons_of_mem _ hs')⟩
  | step_seq_inner _ ih =>
    obtain ⟨h_inner_inv, h_ndef⟩ := h_inv
    exact ⟨ih h_inner_inv, h_ndef⟩
  | step_seq_done =>
    obtain ⟨h_none, h_ndef⟩ := h_inv
    exact ⟨h_none, h_ndef⟩
  | step_seq_exit =>
    obtain ⟨h_none, _⟩ := h_inv; exact h_none
  | step_block_body _ ih =>
    obtain ⟨h_parent, h_inner_inv⟩ := h_inv
    exact ⟨h_parent, ih h_inner_inv⟩
  | step_block_done =>
    obtain ⟨h_parent, _⟩ := h_inv
    show projectStore _ _ y = none
    unfold projectStore; rw [if_neg]; rw [h_parent]; simp
  | step_block_exit_match _ =>
    obtain ⟨h_parent, _⟩ := h_inv
    show projectStore _ _ y = none
    unfold projectStore; rw [if_neg]; rw [h_parent]; simp
  | step_block_exit_mismatch _ =>
    obtain ⟨h_parent, _⟩ := h_inv
    show projectStore _ _ y = none
    unfold projectStore; rw [if_neg]; rw [h_parent]; simp

/-- Trace lift: `NoneAtY` is preserved along a multi-step run. -/
private theorem NoneAtY_star
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {y : P.Ident} {cfg cfg' : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) extendEval cfg cfg')
    (h_inv : NoneAtY (P := P) y cfg) :
    NoneAtY (P := P) y cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ h_step _ ih => exact ih (NoneAtY_step h_step h_inv)

/-- A terminating `.stmt s` run from `ρ` preserves `store y = none` for any
`y ∉ Stmt.definedVars s`. -/
private theorem stmt_run_terminal_preserves_none
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {y : P.Ident} {s : Stmt P (Cmd P)} {ρ ρ' : Env P}
    (h_none : ρ.store y = none)
    (h_ndef : y ∉ Stmt.definedVars (P := P) (C := Cmd P) s)
    (h_run : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ')) :
    ρ'.store y = none :=
  NoneAtY_star h_run ⟨h_none, h_ndef⟩

/-- A name `y` lying in some source statement-list's `Block.initVars` (and hence
shape-free and disjoint from `s`'s own inits) is NOT among the `Block.initVars`
of the residual `(Stmt.hoistLoopPrefixInitsM s σ).1`.  Each residual init is
classified (`hoistLoopPrefixInitsM_initVars_classified`) as either an original
init of `s` (excluded since `y ∉ Stmt.initVars s`) or a freshly generated name
(excluded since `y` is shape-free). -/
private theorem y_not_mem_residual_initVars
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {y : P.Ident} {s : Stmt P (Cmd P)} {σ : StringGenState}
    (h_wf : StringGenState.WF σ)
    (h_unique_s : (Stmt.initVars s).Nodup)
    (h_shapefree_s : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Stmt.initVars s)
    (h_y_not_src : y ∉ Stmt.initVars s)
    (h_y_shapefree : ∀ str : String, y = HasIdent.ident str →
        ¬ Q str) :
    y ∉ Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1 := by
  intro h_mem
  have h_class :=
    (LoopInitHoistLoopArmWF.Stmt.hoistLoopPrefixInitsM_initVars_classified
      hQmint s σ h_wf h_unique_s h_shapefree_s).1 y h_mem
  rcases h_class with h_orig | ⟨str, h_y_eq, h_str_in, _, h_str_Q⟩
  · exact h_y_not_src h_orig
  · -- `y = ident str` with `str` freshly minted (carrying kind `Q`), contradicting
    -- `y`'s kind-freedom.
    exact h_y_shapefree str h_y_eq h_str_Q

/-- A terminating run of the residual block `(Stmt.hoistLoopPrefixInitsM s σ).1`
preserves `store y = none` when `y` is a shape-free source name disjoint from
`s`'s own inits (so `y` is touched by no residual init; `set` cannot fire on an
undefined slot).  This is the hoist-side analogue of
`stmt_run_terminal_preserves_none` for the cons-arm tail, where the hoist store
evolves across the head residual run. -/
private theorem residual_run_terminal_preserves_none
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {y : P.Ident} {s : Stmt P (Cmd P)} {σ : StringGenState} {ρ ρ' : Env P}
    (h_wf : StringGenState.WF σ)
    (h_unique_s : (Stmt.initVars s).Nodup)
    (h_shapefree_s : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Stmt.initVars s)
    (h_no_fd : Stmt.containsFuncDecl s = false)
    (h_y_not_src : y ∉ Stmt.initVars s)
    (h_y_shapefree : ∀ str : String, y = HasIdent.ident str →
        ¬ Q str)
    (h_none : ρ.store y = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Stmt.hoistLoopPrefixInitsM s σ).1 ρ) (.terminal ρ')) :
    ρ'.store y = none := by
  have h_residual_nofd :
      Block.containsFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 = false := by
    rw [Stmt.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_no_fd
  have h_y_not_residual : y ∉ Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1 :=
    y_not_mem_residual_initVars hQmint h_wf h_unique_s h_shapefree_s h_y_not_src h_y_shapefree
  have h_y_not_def : y ∉ Block.definedVars (Stmt.hoistLoopPrefixInitsM s σ).1 := by
    rw [Block.definedVars_eq_initVars_of_no_fd _ h_residual_nofd]; exact h_y_not_residual
  -- `NoneAtY (.stmts residual ρ)` needs per-statement non-membership; derive it
  -- from `y ∉ Block.definedVars residual` via the `definedVars` cons/append shape.
  have h_mem_block : ∀ (ss : List (Stmt P (Cmd P))) (s' : Stmt P (Cmd P)),
      s' ∈ ss → y ∈ Stmt.definedVars (P := P) (C := Cmd P) s' →
      y ∈ Block.definedVars (P := P) (C := Cmd P) ss := by
    intro ss
    induction ss with
    | nil => intro s' hs' _; exact absurd hs' List.not_mem_nil
    | cons hd tl ih =>
      intro s' hs' hc
      rw [Block.definedVars]
      rcases List.mem_cons.mp hs' with h_eq | h_in
      · subst h_eq; exact List.mem_append.mpr (Or.inl hc)
      · exact List.mem_append.mpr (Or.inr (ih s' h_in hc))
  have h_per_stmt : ∀ s' ∈ (Stmt.hoistLoopPrefixInitsM s σ).1,
      y ∉ Stmt.definedVars (P := P) (C := Cmd P) s' := fun s' hs' hc =>
    h_y_not_def (h_mem_block (Stmt.hoistLoopPrefixInitsM s σ).1 s' hs' hc)
  exact NoneAtY_star h_run ⟨h_none, h_per_stmt⟩

/-- A name `y` undefined at block entry and NOT among the block's `initVars`
(under `containsFuncDecl = false`, so `definedVars = initVars`) stays undefined
across a terminating block run.  Used in the §E cons-tail mid-store discharge to
keep a suffix-shaped name `∉ stringGens σ₁` undefined past the head residual run
on the hoist side, where the head residual may itself contain generated `.init`s
(so the `definedVars = initVars`-based no-touch argument is the right tool). -/
private theorem block_run_terminal_preserves_none_of_not_initVars
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {y : P.Ident} {bss : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h_no_fd : Block.containsFuncDecl bss = false)
    (h_y_not_init : y ∉ Block.initVars bss)
    (h_none : ρ.store y = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ) (.terminal ρ')) :
    ρ'.store y = none := by
  have h_y_not_def : y ∉ Block.definedVars bss := by
    rw [Block.definedVars_eq_initVars_of_no_fd _ h_no_fd]; exact h_y_not_init
  have h_mem_block : ∀ (ss : List (Stmt P (Cmd P))) (s' : Stmt P (Cmd P)),
      s' ∈ ss → y ∈ Stmt.definedVars (P := P) (C := Cmd P) s' →
      y ∈ Block.definedVars (P := P) (C := Cmd P) ss := by
    intro ss
    induction ss with
    | nil => intro s' hs' _; exact absurd hs' List.not_mem_nil
    | cons hd tl ih =>
      intro s' hs' hc
      rw [Block.definedVars]
      rcases List.mem_cons.mp hs' with h_eq | h_in
      · subst h_eq; exact List.mem_append.mpr (Or.inl hc)
      · exact List.mem_append.mpr (Or.inr (ih s' h_in hc))
  have h_per_stmt : ∀ s' ∈ bss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s' :=
    fun s' hs' hc => h_y_not_def (h_mem_block bss s' hs' hc)
  exact NoneAtY_star h_run ⟨h_none, h_per_stmt⟩

-- `Stmt.containsFuncDecl s = false → Stmt.noFuncDecl s = true` (and the block
-- sibling).  Bridges the §E precondition `h_no_fd` (stated via
-- `containsFuncDecl`) to the eval-preservation lemmas (stated via `noFuncDecl`).
mutual
private theorem Stmt.noFuncDecl_of_not_containsFuncDecl
    (s : Stmt P (Cmd P)) (h : Stmt.containsFuncDecl s = false) :
    Stmt.noFuncDecl s = true := by
  match s with
  | .cmd c => rw [Stmt.noFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.noFuncDecl]
      rw [Stmt.containsFuncDecl] at h
      exact Block.noFuncDecl_of_not_containsFuncDecl bss h
  | .ite g tss ess md =>
      rw [Stmt.noFuncDecl]
      rw [Stmt.containsFuncDecl, Bool.or_eq_false_iff] at h
      rw [Bool.and_eq_true]
      exact ⟨Block.noFuncDecl_of_not_containsFuncDecl tss h.1,
             Block.noFuncDecl_of_not_containsFuncDecl ess h.2⟩
  | .loop g m inv body md =>
      rw [Stmt.noFuncDecl]
      rw [Stmt.containsFuncDecl] at h
      exact Block.noFuncDecl_of_not_containsFuncDecl body h
  | .exit lbl md => rw [Stmt.noFuncDecl]
  | .funcDecl d md => rw [Stmt.containsFuncDecl] at h; exact absurd h (by simp)
  | .typeDecl t md => rw [Stmt.noFuncDecl]
  termination_by sizeOf s

private theorem Block.noFuncDecl_of_not_containsFuncDecl
    (ss : List (Stmt P (Cmd P))) (h : Block.containsFuncDecl ss = false) :
    Block.noFuncDecl ss = true := by
  match ss with
  | [] => rw [Block.noFuncDecl]
  | s :: rest =>
      rw [Block.noFuncDecl]
      rw [Block.containsFuncDecl, Bool.or_eq_false_iff] at h
      rw [Bool.and_eq_true]
      exact ⟨Stmt.noFuncDecl_of_not_containsFuncDecl s h.1,
             Block.noFuncDecl_of_not_containsFuncDecl rest h.2⟩
  termination_by sizeOf ss
end

/-- Inversion of a labeled block reaching `.exiting`: in addition to the inner
exit run and the projection (as in `block_reaches_exiting`), record that the
inner exit label does NOT match the block's label — the block only PROPAGATES a
mismatched exit (a matching exit would have been caught and terminated).  This
mismatch fact is what the §E `.block` arm needs to replay `step_block_exit_mismatch`
on the hoisted side. -/
private theorem block_some_reaches_exiting_ne
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {label : String} {σ_parent : SemanticStore P}
    {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P (EvalCmd P) extendEval
      (.block (.some label) σ_parent inner) (.exiting lbl ρ')) :
    ∃ lbl_inner ρ_inner,
      StepStmtStar P (EvalCmd P) extendEval inner (.exiting lbl_inner ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      lbl_inner = lbl ∧ (Option.some label : Option String) ≠ Option.some lbl := by
  suffices ∀ src tgt, StepStmtStar P (EvalCmd P) extendEval src tgt →
      ∀ inner lbl ρ', src = .block (.some label) σ_parent inner → tgt = .exiting lbl ρ' →
      ∃ lbl_inner ρ_inner,
        StepStmtStar P (EvalCmd P) extendEval inner (.exiting lbl_inner ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
        lbl_inner = lbl ∧ (Option.some label : Option String) ≠ Option.some lbl from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨lbl_inner, ρ_inner, hexit, heq, hli, hne⟩ := ih _ _ _ rfl htgt
      exact ⟨lbl_inner, ρ_inner, .step _ _ _ h hexit, heq, hli, hne⟩
    | step_block_exit_mismatch h_ne =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, _, .refl _, rfl, rfl, h_ne⟩
      | step _ _ _ h _ => cases h
    | step_block_done | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-! ### §E `.ite` guard-agreement helper

The `.ite` arm must drive the hoisted `.ite` through the SAME branch the source
chose, which requires that the guard `g` evaluates identically on the two
`HoistInv`-related entry stores.  This holds because the guard's variables are
fresh w.r.t. both `A` and `B` (the `namesFreshInExprs` preconditions), so they
lie OUTSIDE `A ∪ B`, where the two stores agree by `HoistInv` component (1);
expression-congruence (`h_wfcongr`) then transports the evaluation. -/

/-- Extract guard-variable disjointness from the `.ite` freshness precondition:
if `names` is fresh in `.ite (.det g) tss ess md`, then no guard variable is in
`names`. -/
private theorem ite_guard_vars_not_mem
    [HasVarsPure P P.Expr]
    {names : List P.Ident} {g : P.Expr}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Block.namesFreshInExprs (P := P) names [.ite (.det g) tss ess md] = true) :
    ∀ x ∈ HasVarsPure.getVars g, x ∉ names := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
    Bool.and_eq_true, ExprOrNondet.getVars] at h
  obtain ⟨⟨h_guard, _⟩, _⟩ := h
  rw [List.all_eq_true] at h_guard
  intro x hx_g hx_names
  exact absurd (freshFromIdents_not_mem (h_guard x hx_names)) (fun h => h hx_g)

/-- Guard agreement: the `.ite` guard evaluates identically on the two
`HoistInv`-related entry stores. -/
private theorem ite_guard_agree
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)} {g : P.Expr}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ_src ρ_hoist : Env P}
    (h_names_fresh : Block.namesFreshInExprs (P := P) A [.ite (.det g) tss ess md] = true)
    (h_names_fresh_B : Block.namesFreshInExprs (P := P) B [.ite (.det g) tss ess md] = true)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_read_def : ∀ x ∈ HasVarsPure.getVars g, ρ_src.store x ≠ none)
    (h_eval_eq : ρ_src.eval = ρ_hoist.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval) :
    ρ_src.eval ρ_src.store g = ρ_hoist.eval ρ_hoist.store g := by
  have h_notA := ite_guard_vars_not_mem (P := P) h_names_fresh
  have h_notB := ite_guard_vars_not_mem (P := P) h_names_fresh_B
  -- Stores agree on every guard variable (each is outside A ∪ B and source-defined).
  have h_store_agree : ∀ x ∈ HasVarsPure.getVars g, ρ_src.store x = ρ_hoist.store x := by
    intro x hx
    exact h_hinv.1 x (h_notA x hx) (h_notB x hx) (h_read_def x hx)
  rw [h_eval_eq]
  exact (h_wfcongr ρ_hoist) g ρ_src.store ρ_hoist.store h_store_agree

/-! ### §E `.cmd` arm closing kit

The `.cmd c` arm of the §E Stmt-IH replays the SAME command `c` on the hoisted
side and shows the resulting stores stay `HoistInv`-related.  The store
transport splits on the command shape: `.init`/`.set` whose target lies outside
`A ∪ B` move both stores by `extendStoreOne` and use
`HoistInv.extend_both_outside_subst`; `.assert`/`.assume`/`.cover` leave the
store fixed so `HoistInv` carries through unchanged.

The disjointness of the `.set`/`.init` target from `A ∪ B` is exactly what the
two modified-variable preconditions `h_mod_disjoint_A`/`h_mod_disjoint_B`
supply: at `[.cmd (.set x ..)]` they reduce to `x ∉ A`/`x ∉ B`, ruling out the
otherwise-unsound case where a `.set` target coincides with a renamed-name set
side.  These lemmas are factored out so the `.cmd` arm of the mutual is a single
application of `cmd_arm`. -/

open StructuredToUnstructuredCorrect in
/-- `InitState` to a function-level `extendStoreOne` equality. -/
private theorem InitState_eq_extendStoreOne
    [DecidableEq P.Ident]
    {σ σ' : SemanticStore P} {y : P.Ident} {v : P.Expr}
    (h_is : InitState P σ y v σ') :
    σ' = extendStoreOne σ y v := by
  cases h_is with
  | init h_none h_some h_other =>
    funext z
    by_cases hzy : z = y
    · subst hzy; rw [h_some]; exact (extendStoreOne_self σ z v).symm
    · rw [h_other z (fun h => hzy h.symm)]
      exact (extendStoreOne_other σ y v z hzy).symm

open StructuredToUnstructuredCorrect in
/-- `UpdateState` to a function-level `extendStoreOne` equality. -/
private theorem UpdateState_eq_extendStoreOne
    [DecidableEq P.Ident]
    {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Expr}
    (h_us : UpdateState P σ x v σ') :
    σ' = extendStoreOne σ x v := by
  cases h_us with
  | update h_was h_post h_other =>
    funext z
    by_cases hzx : z = x
    · subst hzx; rw [h_post]; exact (extendStoreOne_self σ z v).symm
    · rw [h_other z (fun h => hzx h.symm)]
      exact (extendStoreOne_other σ x v z hzx).symm

/-- Invert a single `.stmt (.cmd c) ρ ⟶* .terminal ρ'` run into its `EvalCmd`. -/
private theorem stmt_cmd_terminal_inv
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {c : Cmd P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.cmd c) ρ) (.terminal ρ')) :
    ∃ σ' hf, EvalCmd P ρ.eval ρ.store c σ' hf ∧
      ρ' = { ρ with store := σ', hasFailure := ρ.hasFailure || hf } := by
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_cmd h_eval =>
      cases hr1 with
      | refl => exact ⟨_, _, h_eval, rfl⟩
      | step _ _ _ hd _ => exact nomatch hd

/-- The hoisted residual `.stmts [.cmd c] ρ ⟶* .terminal ρ'` given the EvalCmd. -/
private theorem stmts_single_cmd_run
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {c : Cmd P} {ρ : Env P} {σ' : SemanticStore P} {hf : Bool}
    (h_eval : EvalCmd P ρ.eval ρ.store c σ' hf) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts [.cmd c] ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hf }) := by
  refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
  refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner (StepStmt.step_cmd h_eval)) ?_
  refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
  exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)

open StructuredToUnstructuredCorrect in
/-- Shared closing for the parallel single-target update sub-cases (`.init`,
`.set` outside the subst frame).  The source store moves to
`extendStoreOne ρ_src.store y v`; the hoist replays the SAME command (target
`y ∉ A ∪ B`) and moves to `extendStoreOne ρ_hoist.store y v`. -/
private theorem cmd_init_arm_close
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {c : Cmd P} {y : P.Ident} {v : P.Expr}
    {ρ_src ρ_hoist : Env P} {σ' : SemanticStore P}
    (h_y_notA : y ∉ A) (h_y_notB : y ∉ B)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_hf_eq : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_hoist_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_σ'_eq : σ' = extendStoreOne ρ_src.store y v)
    (h_eval_cmd_hoist :
      EvalCmd P ρ_hoist.eval ρ_hoist.store c (extendStoreOne ρ_hoist.store y v) false) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts [.cmd c] ρ_hoist) cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            (.terminal { ρ_src with store := σ', hasFailure := ρ_src.hasFailure || false }
              : Config P (Cmd P)) = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            (.terminal { ρ_src with store := σ', hasFailure := ρ_src.hasFailure || false }
              : Config P (Cmd P)) = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  have h_hinv_post :
      HoistInv (P := P) A B subst (extendStoreOne ρ_src.store y v)
        (extendStoreOne ρ_hoist.store y v) :=
    HoistInv.extend_both_outside_subst h_y_notA h_y_notB h_subst_wf h_hinv
  have h_run := stmts_single_cmd_run (extendEval := extendEval) h_eval_cmd_hoist
  refine ⟨_, _, h_run, Or.inl ⟨_, rfl, rfl, ?_, ?_, ?_⟩⟩
  · show HoistInv (P := P) A B subst σ' (extendStoreOne ρ_hoist.store y v)
    rw [h_σ'_eq]; exact h_hinv_post
  · show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false)
    rw [h_hf_eq]
  · intro z hz
    show extendStoreOne ρ_hoist.store y v z ≠ none
    have hzy : z ≠ y := fun h => h_y_notB (h ▸ hz)
    have he : extendStoreOne ρ_hoist.store y v z = ρ_hoist.store z :=
      extendStoreOne_other ρ_hoist.store y v z hzy
    rw [he]
    exact h_hoist_bound z hz

/-- Shared closing for the store-fixed (`assert`/`assume`/`cover`) sub-cases.
The hoist replays the SAME command, leaving its store fixed; `HoistInv` carries
through unchanged. -/
private theorem cmd_passive_arm_close
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {c : Cmd P} {hf : Bool}
    {ρ_src ρ_hoist : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_hf_eq : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_hoist_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_eval_cmd_hoist :
      EvalCmd P ρ_hoist.eval ρ_hoist.store c ρ_hoist.store hf) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts [.cmd c] ρ_hoist) cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            (.terminal { ρ_src with store := ρ_src.store, hasFailure := ρ_src.hasFailure || hf }
              : Config P (Cmd P)) = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            (.terminal { ρ_src with store := ρ_src.store, hasFailure := ρ_src.hasFailure || hf }
              : Config P (Cmd P)) = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  have h_run := stmts_single_cmd_run (extendEval := extendEval) h_eval_cmd_hoist
  refine ⟨_, _, h_run, Or.inl ⟨_, rfl, rfl, ?_, ?_, ?_⟩⟩
  · exact h_hinv
  · show (ρ_src.hasFailure || hf) = (ρ_hoist.hasFailure || hf)
    rw [h_hf_eq]
  · intro z hz; exact h_hoist_bound z hz

open StructuredToUnstructuredCorrect in
/-- The §E `.cmd c` arm obligation, isolated, with the two additional
disjointness preconditions `h_mod_disjoint_A`/`h_mod_disjoint_B` over
`Block.modifiedVars`.  Closes ALL eight `EvalCmd` shapes sorry-free. -/
private theorem cmd_arm
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident]
    {Q : String → Prop}
    {extendEval : ExtendEval P}
    (A B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (c : Cmd P)
    (σ : StringGenState)
    {ρ_src ρ_hoist : Env P}
    {cfg_src : Config P (Cmd P)}
    (h_names_fresh : Block.namesFreshInExprs A [.cmd c] = true)
    (h_names_fresh_B : Block.namesFreshInExprs B [.cmd c] = true)
    (h_lhs_disjoint : ∀ y ∈ Block.initVars [.cmd c], y ∉ A)
    (h_extra_disjoint : ∀ y ∈ Block.initVars [.cmd c], y ∉ B)
    (h_mod_disjoint_A : ∀ x ∈ Block.modifiedVars (P := P) (C := Cmd P) [.cmd c], x ∉ A)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars (P := P) (C := Cmd P) [.cmd c], x ∉ B)
    (h_hoist_undef : ∀ y ∈ Block.initVars [.cmd c], ρ_src.store y = none)
    (h_hoist_undef_h : ∀ y ∈ Block.initVars [.cmd c], ρ_hoist.store y = none)
    (_h_src_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (_h_hoist_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_hoist.store (HasIdent.ident (P := P) str) = none)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval_eq    : ρ_src.eval = ρ_hoist.eval)
    (h_hf_eq      : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_hoist_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendEval
                     (.stmt (.cmd c) ρ_src) cfg_src)
    (h_cfg_src    : (∃ ρ_src' : Env P, cfg_src = .terminal ρ_src') ∨
                    (∃ lbl ρ_src', cfg_src = .exiting lbl ρ_src'))
    (h_wfvar      : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr    : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (_h_wfsubst    : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef      : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Stmt.hoistLoopPrefixInitsM (.cmd c) σ).1 ρ_hoist) cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            cfg_src = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            cfg_src = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  classical
  -- Residual is the identity `[.cmd c]`.
  have h_residual : (Stmt.hoistLoopPrefixInitsM (.cmd c) σ).1 = [.cmd c] := by
    rw [Stmt.hoistLoopPrefixInitsM]
  rw [h_residual]
  -- The source run terminates (a single command never exits).
  obtain ⟨ρ_src', h_term⟩ : ∃ ρ_src' : Env P, cfg_src = .terminal ρ_src' := by
    rcases h_cfg_src with h | ⟨lbl, ρe, h_exit⟩
    · exact h
    · subst h_exit
      exact absurd h_run_src (by
        intro h
        cases h with
        | step _ _ _ h1 hr1 =>
          cases h1 with
          | step_cmd _ => cases hr1 with | step _ _ _ hd _ => exact nomatch hd)
  subst h_term
  -- Invert into the EvalCmd evidence.
  obtain ⟨σ', hf, h_eval, h_ρsrc'⟩ := stmt_cmd_terminal_inv h_run_src
  subst h_ρsrc'
  -- Goal: produce ρ_h' and the terminal-disjunct witness for the hoist replay of c.
  -- For every shape, the hoist replays the SAME command c.
  cases c with
  | init y ty rhs md =>
    -- definedVars (.init y) = [y]; Block.initVars [.cmd (.init y..)] = [y].
    have h_y_init : y ∈ Block.initVars (P := P) [.cmd (.init y ty rhs md)] := by
      simp [Block.initVars, Stmt.initVars]
    have h_y_notA : y ∉ A := h_lhs_disjoint y h_y_init
    have h_y_notB : y ∉ B := h_extra_disjoint y h_y_init
    have h_y_src_none : ρ_src.store y = none := h_hoist_undef y h_y_init
    -- The hoist-side undefinedness now comes from the COMPANION invariant
    -- `h_hoist_undef_h` (the guarded frame no longer carries the none⇒none route).
    have h_y_hoist_none : ρ_hoist.store y = none := h_hoist_undef_h y h_y_init
    -- The RHS-freshness facts for A and B (so rhs eval agrees across stores).
    have h_rhs_freshA : ∀ z ∈ A, z ∉ ExprOrNondet.getVars (P := P) rhs := by
      intro z hz
      have h := h_names_fresh
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        List.all_eq_true] at h
      exact freshFromIdents_not_mem (h z hz)
    have h_rhs_freshB : ∀ z ∈ B, z ∉ ExprOrNondet.getVars (P := P) rhs := by
      intro z hz
      have h := h_names_fresh_B
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        List.all_eq_true] at h
      exact freshFromIdents_not_mem (h z hz)
    -- Stores agree on every source-DEFINED variable read by rhs (each is outside
    -- A ∪ B); the guard `σ_src x ≠ none` is supplied by the caller from the RHS
    -- evaluation success.
    have h_rhs_agree : ∀ x ∈ ExprOrNondet.getVars (P := P) rhs,
        ρ_src.store x ≠ none → ρ_src.store x = ρ_hoist.store x := by
      intro x hx h_x_ne
      refine h_hinv.1 x ?_ ?_ h_x_ne
      · intro hxA; exact h_rhs_freshA x hxA hx
      · intro hxB; exact h_rhs_freshB x hxB hx
    -- Build the hoist init + the post HoistInv.  The init target y ∉ A ∪ B, so
    -- the parallel update at y uses `extend_both_outside_subst`.
    cases h_eval with
    | eval_init h_eval_src h_is_src h_wfvar_src h_wfcongr_src =>
      rename_i v e
      -- rhs = .det e, getVars rhs = getVars e.  The RHS evaluation succeeds
      -- (`h_eval_src`), so every read var is source-defined — discharging the
      -- guarded frame.
      have h_e_read_def : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x ≠ none :=
        read_vars_def_of_eval (h_wfdef ρ_src) h_eval_src
      have h_e_agree : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x = ρ_hoist.store x := by
        intro x hx
        exact h_rhs_agree x (by show x ∈ ExprOrNondet.getVars (.det e); exact hx)
          (h_e_read_def x hx)
      have h_eval_hoist : ρ_hoist.eval ρ_hoist.store e = .some v := by
        have h_eq : ρ_hoist.eval ρ_src.store e = ρ_hoist.eval ρ_hoist.store e :=
          (h_wfcongr ρ_hoist) e ρ_src.store ρ_hoist.store h_e_agree
        rw [← h_eq, ← h_eval_eq]; exact h_eval_src
      -- σ' = extendStoreOne ρ_src.store y v (from InitState).
      have h_σ'_eq : σ' = extendStoreOne ρ_src.store y v := InitState_eq_extendStoreOne h_is_src
      -- Hoist InitState at y (ρ_hoist.store y = none).
      have h_is_hoist : InitState P ρ_hoist.store y v (extendStoreOne ρ_hoist.store y v) :=
        InitState.init h_y_hoist_none (extendStoreOne_self ρ_hoist.store y v)
          (fun z hz => extendStoreOne_other ρ_hoist.store y v z (fun h => hz h.symm))
      have h_wfvar_hoist : WellFormedSemanticEvalVar ρ_hoist.eval := h_wfvar ρ_hoist
      have h_wfcongr_hoist : WellFormedSemanticEvalExprCongr ρ_hoist.eval := h_wfcongr ρ_hoist
      have h_eval_cmd_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.init y ty (.det e) md)
            (extendStoreOne ρ_hoist.store y v) false :=
        EvalCmd.eval_init h_eval_hoist h_is_hoist h_wfvar_hoist h_wfcongr_hoist
      exact cmd_init_arm_close (v := v) h_y_notA h_y_notB h_subst_wf h_hinv h_hf_eq h_hoist_bound
        h_σ'_eq h_eval_cmd_hoist
    | eval_init_unconstrained h_is_src h_wfvar_src =>
      rename_i v
      have h_σ'_eq : σ' = extendStoreOne ρ_src.store y v := InitState_eq_extendStoreOne h_is_src
      have h_is_hoist : InitState P ρ_hoist.store y v (extendStoreOne ρ_hoist.store y v) :=
        InitState.init h_y_hoist_none (extendStoreOne_self ρ_hoist.store y v)
          (fun z hz => extendStoreOne_other ρ_hoist.store y v z (fun h => hz h.symm))
      have h_wfvar_hoist : WellFormedSemanticEvalVar ρ_hoist.eval := h_wfvar ρ_hoist
      have h_eval_cmd_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.init y ty .nondet md)
            (extendStoreOne ρ_hoist.store y v) false :=
        EvalCmd.eval_init_unconstrained h_is_hoist h_wfvar_hoist
      exact cmd_init_arm_close (v := v) h_y_notA h_y_notB h_subst_wf h_hinv h_hf_eq h_hoist_bound
        h_σ'_eq h_eval_cmd_hoist
  | set x rhs md =>
    -- The hoist replays `.set x`.  `Cmd.modifiedVars (.set x ..) = [x]`, so the
    -- two new disjointness hyps give `x ∉ A` and `x ∉ B` directly: the `.set`
    -- target can never coincide with a renamed-name set side.
    have h_x_mod : x ∈ Block.modifiedVars (P := P) (C := Cmd P) [.cmd (.set x rhs md)] := by
      simp [Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.modifiedVars, Cmd.modifiedVars]
    have hxA : x ∉ A := h_mod_disjoint_A x h_x_mod
    have hxB : x ∉ B := h_mod_disjoint_B x h_x_mod
    -- rhs-freshness ⇒ eval agreement on source-DEFINED rhs vars (guard supplied
    -- by the caller from the RHS evaluation success).
    have h_rhs_agree : ∀ z ∈ ExprOrNondet.getVars (P := P) rhs,
        ρ_src.store z ≠ none → ρ_src.store z = ρ_hoist.store z := by
      intro z hz h_z_ne
      refine h_hinv.1 z ?_ ?_ h_z_ne
      · intro hzA
        have h := h_names_fresh
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzA) hz
      · intro hzB
        have h := h_names_fresh_B
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzB) hz
    cases h_eval with
    | eval_set h_eval_src h_upd_src h_wfvar_src h_wfcongr_src =>
      rename_i v e
      have h_e_read_def : ∀ z ∈ HasVarsPure.getVars (P := P) e, ρ_src.store z ≠ none :=
        read_vars_def_of_eval (h_wfdef ρ_src) h_eval_src
      have h_e_agree : ∀ z ∈ HasVarsPure.getVars (P := P) e,
          ρ_src.store z = ρ_hoist.store z := fun z hz =>
        h_rhs_agree z (by show z ∈ ExprOrNondet.getVars (.det e); exact hz) (h_e_read_def z hz)
      have h_eval_hoist : ρ_hoist.eval ρ_hoist.store e = .some v := by
        have h_eq : ρ_hoist.eval ρ_src.store e = ρ_hoist.eval ρ_hoist.store e :=
          (h_wfcongr ρ_hoist) e ρ_src.store ρ_hoist.store h_e_agree
        rw [← h_eq, ← h_eval_eq]; exact h_eval_src
      -- Build hoist UpdateState at x (defined: x was previously bound, so the
      -- guarded frame at x is dischargeable).
      have h_x_some_src : ∃ v_old, ρ_src.store x = some v_old := by
        cases h_upd_src with | update h1 _ _ => exact ⟨_, h1⟩
      obtain ⟨v_old, h_x_some_src⟩ := h_x_some_src
      have h_x_src_eq_hoist : ρ_src.store x = ρ_hoist.store x :=
        h_hinv.1 x hxA hxB (by rw [h_x_some_src]; exact Option.some_ne_none v_old)
      have h_x_hoist_some : ρ_hoist.store x = some v_old := by
        rw [← h_x_src_eq_hoist]; exact h_x_some_src
      have h_upd_hoist :
          UpdateState P ρ_hoist.store x v (extendStoreOne ρ_hoist.store x v) :=
        UpdateState.update h_x_hoist_some (extendStoreOne_self ρ_hoist.store x v)
          (fun z hz => extendStoreOne_other ρ_hoist.store x v z (fun h => hz h.symm))
      have h_eval_cmd_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.set x (.det e) md)
            (extendStoreOne ρ_hoist.store x v) false :=
        EvalCmd.eval_set h_eval_hoist h_upd_hoist (h_wfvar ρ_hoist) (h_wfcongr ρ_hoist)
      have h_σ'_eq : σ' = extendStoreOne ρ_src.store x v :=
        UpdateState_eq_extendStoreOne h_upd_src
      exact cmd_init_arm_close (v := v) hxA hxB h_subst_wf h_hinv h_hf_eq h_hoist_bound
        h_σ'_eq h_eval_cmd_hoist
    | eval_set_nondet h_upd_src h_wfvar_src =>
      rename_i v
      have h_x_some_src : ∃ v_old, ρ_src.store x = some v_old := by
        cases h_upd_src with | update h1 _ _ => exact ⟨_, h1⟩
      obtain ⟨v_old, h_x_some_src⟩ := h_x_some_src
      have h_x_src_eq_hoist : ρ_src.store x = ρ_hoist.store x :=
        h_hinv.1 x hxA hxB (by rw [h_x_some_src]; exact Option.some_ne_none v_old)
      have h_x_hoist_some : ρ_hoist.store x = some v_old := by
        rw [← h_x_src_eq_hoist]; exact h_x_some_src
      have h_upd_hoist :
          UpdateState P ρ_hoist.store x v (extendStoreOne ρ_hoist.store x v) :=
        UpdateState.update h_x_hoist_some (extendStoreOne_self ρ_hoist.store x v)
          (fun z hz => extendStoreOne_other ρ_hoist.store x v z (fun h => hz h.symm))
      have h_eval_cmd_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.set x .nondet md)
            (extendStoreOne ρ_hoist.store x v) false :=
        EvalCmd.eval_set_nondet h_upd_hoist (h_wfvar ρ_hoist)
      have h_σ'_eq : σ' = extendStoreOne ρ_src.store x v :=
        UpdateState_eq_extendStoreOne h_upd_src
      exact cmd_init_arm_close (v := v) hxA hxB h_subst_wf h_hinv h_hf_eq h_hoist_bound
        h_σ'_eq h_eval_cmd_hoist
  | assert albl e md =>
    -- Condition vars are fresh from A and B (from h_names_fresh / _B), so the
    -- guard evaluates identically on the HoistInv-related stores — at every
    -- source-DEFINED read var (guard supplied from the condition eval success).
    have h_e_agree : ∀ z ∈ HasVarsPure.getVars (P := P) e,
        ρ_src.store z ≠ none → ρ_src.store z = ρ_hoist.store z := by
      intro z hz h_z_ne
      refine h_hinv.1 z ?_ ?_ h_z_ne
      · intro hzA
        have h := h_names_fresh
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzA) hz
      · intro hzB
        have h := h_names_fresh_B
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzB) hz
    have h_guard_transport : ∀ w, ρ_src.eval ρ_src.store e = some w →
        ρ_hoist.eval ρ_hoist.store e = ρ_src.eval ρ_src.store e := by
      intro w h_e_w
      have h_read_def := read_vars_def_of_eval (h_wfdef ρ_src) h_e_w
      have h_agree : ∀ z ∈ HasVarsPure.getVars (P := P) e, ρ_src.store z = ρ_hoist.store z :=
        fun z hz => h_e_agree z hz (h_read_def z hz)
      have h_eq : ρ_hoist.eval ρ_src.store e = ρ_hoist.eval ρ_hoist.store e :=
        (h_wfcongr ρ_hoist) e ρ_src.store ρ_hoist.store h_agree
      rw [← h_eq, ← h_eval_eq]
    cases h_eval with
    | eval_assert_pass h_tt h_wfb h_wfc =>
      have h_eval_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.assert albl e md) ρ_hoist.store false :=
        EvalCmd.eval_assert_pass (by rw [h_guard_transport _ h_tt]; exact h_tt)
          (h_eval_eq ▸ h_wfb) (h_wfcongr ρ_hoist)
      exact cmd_passive_arm_close h_hinv h_hf_eq h_hoist_bound h_eval_hoist
    | eval_assert_fail h_ff h_wfb h_wfc =>
      have h_eval_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.assert albl e md) ρ_hoist.store true :=
        EvalCmd.eval_assert_fail (by rw [h_guard_transport _ h_ff]; exact h_ff)
          (h_eval_eq ▸ h_wfb) (h_wfcongr ρ_hoist)
      exact cmd_passive_arm_close h_hinv h_hf_eq h_hoist_bound h_eval_hoist
  | assume albl e md =>
    have h_e_agree : ∀ z ∈ HasVarsPure.getVars (P := P) e,
        ρ_src.store z ≠ none → ρ_src.store z = ρ_hoist.store z := by
      intro z hz h_z_ne
      refine h_hinv.1 z ?_ ?_ h_z_ne
      · intro hzA
        have h := h_names_fresh
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzA) hz
      · intro hzB
        have h := h_names_fresh_B
        simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
          List.all_eq_true] at h
        exact freshFromIdents_not_mem (h z hzB) hz
    cases h_eval with
    | eval_assume h_tt h_wfb h_wfc =>
      have h_read_def := read_vars_def_of_eval (h_wfdef ρ_src) h_tt
      have h_agree : ∀ z ∈ HasVarsPure.getVars (P := P) e, ρ_src.store z = ρ_hoist.store z :=
        fun z hz => h_e_agree z hz (h_read_def z hz)
      have h_guard_transport : ρ_hoist.eval ρ_hoist.store e = ρ_src.eval ρ_src.store e := by
        have h_eq : ρ_hoist.eval ρ_src.store e = ρ_hoist.eval ρ_hoist.store e :=
          (h_wfcongr ρ_hoist) e ρ_src.store ρ_hoist.store h_agree
        rw [← h_eq, ← h_eval_eq]
      have h_eval_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.assume albl e md) ρ_hoist.store false :=
        EvalCmd.eval_assume (by rw [h_guard_transport]; exact h_tt)
          (h_eval_eq ▸ h_wfb) (h_wfcongr ρ_hoist)
      exact cmd_passive_arm_close h_hinv h_hf_eq h_hoist_bound h_eval_hoist
  | cover albl e md =>
    cases h_eval with
    | eval_cover h_wfb =>
      have h_eval_hoist :
          EvalCmd P ρ_hoist.eval ρ_hoist.store (.cover albl e md) ρ_hoist.store false :=
        EvalCmd.eval_cover (h_eval_eq ▸ h_wfb)
      exact cmd_passive_arm_close h_hinv h_hf_eq h_hoist_bound h_eval_hoist

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
mutual

/-- §E Stmt-level forward simulation IH (sum-typed conclusion), stated over the
MONADIC pass `Stmt.hoistLoopPrefixInitsM` at an ARBITRARY input generator state
`σ`.

For a single statement `s` with the front-end shape preconditions, every
source run `.stmt s ρ_src ⟶* cfg_src` whose final config is either
`.terminal ρ_src'` or `.exiting lbl ρ_src'` admits a matching hoisted run
`.stmts (Stmt.hoistLoopPrefixInitsM s σ).1 ρ_hoist ⟶* cfg_hoist` to a config
of the same shape (terminal or exiting with the same label), carrying
`HoistInv A B subst` and `hasFailure` agreement.

Quantifying over `σ` (rather than fixing `σ = emp` via the pure wrapper) lets
the `cons`/`.ite` arms recurse: the tail/else IH instantiates at the ADVANCED
state `σ' = (Stmt.hoistLoopPrefixInitsM s σ).2`, where the monadic residual
genuinely lives.  The pure wrapper `Stmt.hoistLoopPrefixInits s` is the
`σ = emp` specialization, so the top-level theorem instantiates this lemma at
`σ := StringGenState.emp`.

`h_wf_σ` is the generator-state well-formedness carried through the threading;
`h_src_namesFreshFromσ` records that every generated label already present in
`σ` (and hence its corresponding identifier) is disjoint from the source
program's frame names `A`, extra names `B`, and `.init` LHS names.  At
`σ = emp` the generated-labels list is empty, so this precondition is
vacuously true.

Three further preconditions support the per-arm reproofs:
`h_names_fresh_B` is the `B`-side analogue of `h_names_fresh` — the extra
names `B` (the hoisted-prelude targets) are fresh in every guard and RHS
expression of the source statement, which the loop/conditional arms need to
transport guard evaluation across the `HoistInv`-related stores.
`h_src_shapefree` records that any source identifier with the generator's
`_<digits>` suffix shape is disjoint from `A`, `B`, and the `.init` LHS names;
this is the well-formedness assumption that front-end source names never
collide with the generator's freshly-minted naming scheme.  `h_subst_wf`
records that every substitution pair `(a, b)` relates an `A`-name to a
`B`-name.

The sum-typed conclusion is required by the `.block` arm: the body of
a labeled block can produce `.exiting lbl_inner` for `lbl_inner ≠ lbl`,
which propagates as `.exiting lbl_inner` at the outer block level. The
old terminal-only conclusion could not transport such body subtraces. -/
private theorem Stmt.hoistLoopPrefixInits_preserves {Q : String → Prop}
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {extendEval : ExtendEval P}
    (A : List P.Ident)
    (B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (s : Stmt P (Cmd P))
    (σ : StringGenState)
    {ρ_src ρ_hoist : Env P}
    {cfg_src : Config P (Cmd P)}
    (h_no_nd      : Stmt.containsNondetLoop s = false)
    (h_no_fd      : Stmt.containsFuncDecl s = false)
    (h_no_inv     : Stmt.loopHasNoInvariants s = true)
    (h_no_measure : Stmt.loopMeasureNone s = true)
    (h_exprs_shapefree : Block.exprsShapeFree (P := P) Q [s])
    (h_unique     : Block.uniqueInits [s])
    (h_fresh      : Block.hoistedNamesFreshInRhsAndGuards (P := P) [s] = true)
    (h_names_fresh : Block.namesFreshInExprs A [s] = true)
    (h_names_fresh_B : Block.namesFreshInExprs B [s] = true)
    (h_lhs_disjoint : ∀ y ∈ Block.initVars [s], y ∉ A)
    (h_extra_disjoint : ∀ y ∈ Block.initVars [s], y ∉ B)
    (h_mod_disjoint_A : ∀ x ∈ Block.modifiedVars [s], x ∉ A)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars [s], x ∉ B)
    (h_hoist_undef : ∀ y ∈ Block.initVars [s], ρ_src.store y = none)
    (h_hoist_undef_h : ∀ y ∈ Block.initVars [s], ρ_hoist.store y = none)
    (h_src_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_hoist_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_hoist.store (HasIdent.ident (P := P) str) = none)
    (h_wf_σ       : StringGenState.WF σ)
    (h_src_namesFreshFromσ :
      ∀ str ∈ StringGenState.stringGens σ,
        HasIdent.ident (P := P) str ∉ A ∧
        HasIdent.ident (P := P) str ∉ B ∧
        HasIdent.ident (P := P) str ∉ Block.initVars [s])
    (h_src_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ A ∧
        HasIdent.ident (P := P) str ∉ B ∧
        HasIdent.ident (P := P) str ∉ Block.initVars [s] ∧
        HasIdent.ident (P := P) str ∉ Block.modifiedVars [s])
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval_eq    : ρ_src.eval = ρ_hoist.eval)
    (h_hf_eq      : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_hoist_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendEval
                     (.stmt s ρ_src) cfg_src)
    (h_cfg_src    : (∃ ρ_src' : Env P, cfg_src = .terminal ρ_src') ∨
                    (∃ lbl ρ_src', cfg_src = .exiting lbl ρ_src'))
    (h_wfvar      : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr    : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst    : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef      : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Stmt.hoistLoopPrefixInitsM s σ).1 ρ_hoist) cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            cfg_src = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            cfg_src = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  classical
  match h_match : s with
  | .cmd c =>
    subst h_match
    -- Identity residual `[.cmd c]`.  A single command cannot exit, so the source
    -- run terminates via one `EvalCmd`; the hoisted side replays the SAME command
    -- and the resulting stores stay `HoistInv`-related.  The store transport
    -- splits on the command shape: `.init`/`.set` whose target lies outside the
    -- substitution use `HoistInv.extend_both_outside_subst`; the remaining
    -- `.assert`/`.assume`/`.cover` leave the store fixed.  The `.set` target
    -- cannot coincide with a substitution-pair side because the modified-variable
    -- disjointness preconditions force it outside `A ∪ B`.  All eight shapes are
    -- discharged by the isolated `cmd_arm`.
    exact cmd_arm A B subst c σ h_names_fresh h_names_fresh_B h_lhs_disjoint
      h_extra_disjoint h_mod_disjoint_A h_mod_disjoint_B h_hoist_undef h_hoist_undef_h
      h_src_store_shapefree h_hoist_store_shapefree
      h_subst_wf
      h_hinv h_eval_eq h_hf_eq h_hoist_bound h_run_src h_cfg_src h_wfvar h_wfcongr h_wfsubst h_wfdef
  | .block lbl bss md =>
    subst h_match
    -- === Decompose the §E preconditions for `[.block lbl bss md]` to `bss`. ===
    -- Every structural Bool walker on `.block` reduces to its body, and
    -- `Block.initVars [.block lbl bss md] = Block.initVars bss`.
    have h_iv_eq : Block.initVars [Stmt.block lbl bss md] = Block.initVars bss := by
      simp only [Block.initVars, Stmt.initVars, List.append_nil]
    have h_mod_eq : Block.modifiedVars [Stmt.block lbl bss md] = Block.modifiedVars bss := by
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil]
    have h_nd_bss : Block.containsNondetLoop bss = false := by
      simpa only [Block.containsNondetLoop, Stmt.containsNondetLoop, Bool.or_false] using h_no_nd
    have h_fd_bss : Block.containsFuncDecl bss = false := by
      simpa only [Block.containsFuncDecl, Stmt.containsFuncDecl, Bool.or_false] using h_no_fd
    have h_inv_bss : Block.loopHasNoInvariants bss = true := by
      simpa only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.and_true] using h_no_inv
    have h_measure_bss : Block.loopMeasureNone bss = true := by
      simpa only [Block.loopMeasureNone, Stmt.loopMeasureNone, Bool.and_true] using h_no_measure
    have h_exprs_shapefree_bss : Block.exprsShapeFree (P := P) Q bss := by
      have h := h_exprs_shapefree
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree] at h
      exact h.1
    have h_unique_bss : Block.uniqueInits bss := by
      show (Block.initVars bss).Nodup
      have : Block.uniqueInits [Stmt.block lbl bss md] =
          (Block.initVars [Stmt.block lbl bss md]).Nodup := rfl
      rw [this, h_iv_eq] at h_unique; exact h_unique
    have h_fresh_bss : Block.hoistedNamesFreshInRhsAndGuards (P := P) bss = true := by
      have h_fresh_unfold := h_fresh
      unfold Block.hoistedNamesFreshInRhsAndGuards at h_fresh_unfold ⊢
      rw [Bool.and_eq_true] at h_fresh_unfold ⊢
      obtain ⟨h_guards, h_nf⟩ := h_fresh_unfold
      refine ⟨?_, ?_⟩
      · simpa only [Block.hoistedNamesFreshInGuards, Stmt.hoistedNamesFreshInGuards,
          Bool.and_true] using h_guards
      · -- `namesFreshInRhsExprs (initVars [.block..]) [.block..] = namesFreshInRhsExprs (initVars bss) bss`.
        have : Block.namesFreshInRhsExprs (Block.initVars [Stmt.block lbl bss md])
            [Stmt.block lbl bss md] =
            Block.namesFreshInRhsExprs (Block.initVars bss) bss := by
          simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true, h_iv_eq]
        rwa [this] at h_nf
    have h_names_fresh_bss : Block.namesFreshInExprs A bss = true := by
      simpa only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true] using h_names_fresh
    have h_names_fresh_B_bss : Block.namesFreshInExprs B bss = true := by
      simpa only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true] using h_names_fresh_B
    have h_lhs_disjoint_bss : ∀ y ∈ Block.initVars bss, y ∉ A := fun y hy =>
      h_lhs_disjoint y (h_iv_eq ▸ hy)
    have h_extra_disjoint_bss : ∀ y ∈ Block.initVars bss, y ∉ B := fun y hy =>
      h_extra_disjoint y (h_iv_eq ▸ hy)
    have h_mod_disjoint_A_bss : ∀ x ∈ Block.modifiedVars bss, x ∉ A := fun x hx =>
      h_mod_disjoint_A x (h_mod_eq ▸ hx)
    have h_mod_disjoint_B_bss : ∀ x ∈ Block.modifiedVars bss, x ∉ B := fun x hx =>
      h_mod_disjoint_B x (h_mod_eq ▸ hx)
    have h_hoist_undef_bss : ∀ y ∈ Block.initVars bss, ρ_src.store y = none := fun y hy =>
      h_hoist_undef y (h_iv_eq ▸ hy)
    have h_hoist_undef_h_bss : ∀ y ∈ Block.initVars bss, ρ_hoist.store y = none := fun y hy =>
      h_hoist_undef_h y (h_iv_eq ▸ hy)
    have h_src_fresh_bss :
        ∀ str ∈ StringGenState.stringGens σ,
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
      intro str hstr
      obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
      exact ⟨hA, hB, fun h => hiv (h_iv_eq ▸ h)⟩
    have h_src_shapefree_bss :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars bss ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars bss := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (h_iv_eq ▸ h), fun h => hmv (h_mod_eq ▸ h)⟩
    -- === Rewrite the residual to the singleton hoisted `.block`. ===
    have h_block_out :
        (Stmt.hoistLoopPrefixInitsM (.block lbl bss md) σ).1 =
          [Stmt.block lbl (Block.hoistLoopPrefixInitsM bss σ).1 md] :=
      Stmt.hoistLoopPrefixInitsM_block_out lbl bss md σ
    rw [h_block_out]
    -- === Invert the SOURCE run: `.stmt (.block lbl bss md) ρ_src` enters the
    --     block scope, runs `bss`, then projects on exit. ===
    cases h_run_src with
    | refl => rcases h_cfg_src with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact nomatch h
    | step _ _ _ h1 hr1 =>
      cases h1
      -- now `hr1 : .block (.some lbl) ρ_src.store (.stmts bss ρ_src) ⟶* cfg_src`.
      rcases h_cfg_src with ⟨ρ_src', h_t⟩ | ⟨lbl_e, ρ_src', h_e⟩
      · -- TERMINAL: inner reaches terminal, or exits with matching label.
        subst h_t
        rcases block_some_reaches_terminal P (EvalCmd P) extendEval hr1 with
          ⟨ρ_inner, h_inner_run, h_proj⟩ | ⟨ρ_inner, h_inner_run, h_proj⟩
        · -- inner terminates.
          obtain ⟨ρ_h', cfg_hoist, h_body_hoist, h_outcome⟩ :=
            Block.hoistLoopPrefixInits_preserves hQmint A B subst bss σ
              h_nd_bss h_fd_bss h_inv_bss h_measure_bss h_exprs_shapefree_bss h_unique_bss h_fresh_bss
              h_names_fresh_bss h_names_fresh_B_bss h_lhs_disjoint_bss h_extra_disjoint_bss
              h_mod_disjoint_A_bss h_mod_disjoint_B_bss
              h_hoist_undef_bss h_hoist_undef_h_bss
              h_src_store_shapefree h_hoist_store_shapefree
              h_wf_σ h_src_fresh_bss h_src_shapefree_bss h_subst_wf h_hinv
              h_eval_eq h_hf_eq h_hoist_bound h_inner_run (Or.inl ⟨ρ_inner, rfl⟩)
              h_wfvar h_wfcongr h_wfsubst h_wfdef
          obtain ⟨h_cfg_h_eq, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :
                cfg_hoist = .terminal ρ_h' ∧
                HoistInv (P := P) A B subst ρ_inner.store ρ_h'.store ∧
                ρ_inner.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
            rcases h_outcome with ⟨r, hr1', hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1', _, _, _, _⟩
            · have : r = ρ_inner := by simp only [Config.terminal.injEq] at hr1'; exact hr1'.symm
              subst this; exact ⟨hr2, hr3, hr4, hr5⟩
            · exact absurd hr1' (by simp)
          subst h_cfg_h_eq
          subst h_proj
          refine ⟨{ ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store },
            .terminal { ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store }, ?_,
            Or.inl ⟨_, rfl, rfl, HoistInv.project_both h_hinv h_hinv_inner, h_hf_inner, ?_⟩⟩
          · -- drive the hoisted block: enter, run body, done.
            refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_block) ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ []
                (block_inner_star P (EvalCmd P) extendEval _ _ _ _ h_body_hoist)) ?_
            refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_block_done) ?_
            refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
            exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (.refl _)
          · -- B-boundedness survives projection: each b ∈ B is in ρ_hoist.store
            -- (h_hoist_bound) so the parent slot is `some`, hence projectStore keeps
            -- the inner value, which is `some` by h_bound_inner.
            intro y hy
            show projectStore ρ_hoist.store ρ_h'.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_hoist_bound y hy)
              | some _ => simp
            rw [h_parent_some]; exact h_bound_inner y hy
        · -- inner exits with the matching label `lbl`: block catches it, terminates.
          obtain ⟨ρ_h', cfg_hoist, h_body_hoist, h_outcome⟩ :=
            Block.hoistLoopPrefixInits_preserves hQmint A B subst bss σ
              h_nd_bss h_fd_bss h_inv_bss h_measure_bss h_exprs_shapefree_bss h_unique_bss h_fresh_bss
              h_names_fresh_bss h_names_fresh_B_bss h_lhs_disjoint_bss h_extra_disjoint_bss
              h_mod_disjoint_A_bss h_mod_disjoint_B_bss
              h_hoist_undef_bss h_hoist_undef_h_bss
              h_src_store_shapefree h_hoist_store_shapefree
              h_wf_σ h_src_fresh_bss h_src_shapefree_bss h_subst_wf h_hinv
              h_eval_eq h_hf_eq h_hoist_bound h_inner_run (Or.inr ⟨lbl, ρ_inner, rfl⟩)
              h_wfvar h_wfcongr h_wfsubst h_wfdef
          obtain ⟨h_cfg_h_eq, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :
                cfg_hoist = .exiting lbl ρ_h' ∧
                HoistInv (P := P) A B subst ρ_inner.store ρ_h'.store ∧
                ρ_inner.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
            rcases h_outcome with ⟨r, hr1', _, _, _, _⟩ | ⟨l, r, hr1', hr2, hr3, hr4, hr5⟩
            · exact absurd hr1'.symm (by simp)
            · obtain ⟨hl, hr_eq⟩ : l = lbl ∧ r = ρ_inner := by
                simp only [Config.exiting.injEq] at hr1'; exact ⟨hr1'.1.symm, hr1'.2.symm⟩
              subst hl; subst hr_eq; exact ⟨hr2, hr3, hr4, hr5⟩
          subst h_cfg_h_eq
          subst h_proj
          refine ⟨{ ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store },
            .terminal { ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store }, ?_,
            Or.inl ⟨_, rfl, rfl, HoistInv.project_both h_hinv h_hinv_inner, h_hf_inner, ?_⟩⟩
          · refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_block) ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ []
                (block_inner_star P (EvalCmd P) extendEval _ _ _ _ h_body_hoist)) ?_
            refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner (StepStmt.step_block_exit_match rfl)) ?_
            refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
            exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (.refl _)
          · intro y hy
            show projectStore ρ_hoist.store ρ_h'.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_hoist_bound y hy)
              | some _ => simp
            rw [h_parent_some]; exact h_bound_inner y hy
      · -- EXITING: inner exits with a NON-matching label, which propagates.
        subst h_e
        obtain ⟨lbl_inner, ρ_inner, h_inner_run, h_proj, h_li_eq, h_label_ne⟩ :=
          block_some_reaches_exiting_ne (extendEval := extendEval) hr1
        subst h_li_eq
        obtain ⟨ρ_h', cfg_hoist, h_body_hoist, h_outcome⟩ :=
          Block.hoistLoopPrefixInits_preserves hQmint A B subst bss σ
            h_nd_bss h_fd_bss h_inv_bss h_measure_bss h_exprs_shapefree_bss h_unique_bss h_fresh_bss
            h_names_fresh_bss h_names_fresh_B_bss h_lhs_disjoint_bss h_extra_disjoint_bss
            h_mod_disjoint_A_bss h_mod_disjoint_B_bss
            h_hoist_undef_bss h_hoist_undef_h_bss
            h_src_store_shapefree h_hoist_store_shapefree
            h_wf_σ h_src_fresh_bss h_src_shapefree_bss h_subst_wf h_hinv
            h_eval_eq h_hf_eq h_hoist_bound h_inner_run (Or.inr ⟨lbl_inner, ρ_inner, rfl⟩)
            h_wfvar h_wfcongr h_wfsubst h_wfdef
        obtain ⟨h_cfg_h_eq, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :
              cfg_hoist = .exiting lbl_inner ρ_h' ∧
              HoistInv (P := P) A B subst ρ_inner.store ρ_h'.store ∧
              ρ_inner.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
          rcases h_outcome with ⟨r, hr1', _, _, _, _⟩ | ⟨l, r, hr1', hr2, hr3, hr4, hr5⟩
          · exact absurd hr1'.symm (by simp)
          · obtain ⟨hl, hr_eq⟩ : l = lbl_inner ∧ r = ρ_inner := by
              simp only [Config.exiting.injEq] at hr1'; exact ⟨hr1'.1.symm, hr1'.2.symm⟩
            subst hl; subst hr_eq; exact ⟨hr2, hr3, hr4, hr5⟩
        subst h_cfg_h_eq
        subst h_proj
        refine ⟨{ ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store },
          .exiting lbl_inner { ρ_h' with store := projectStore ρ_hoist.store ρ_h'.store }, ?_,
          Or.inr ⟨lbl_inner, _, rfl, rfl, HoistInv.project_both h_hinv h_hinv_inner, h_hf_inner, ?_⟩⟩
        · refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
          refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) extendEval _ _ []
              (block_inner_star P (EvalCmd P) extendEval _ _ _ _ h_body_hoist)) ?_
          refine ReflTrans.step _ _ _
            (StepStmt.step_seq_inner (StepStmt.step_block_exit_mismatch h_label_ne)) ?_
          exact ReflTrans.step _ _ _ StepStmt.step_seq_exit (.refl _)
        · intro y hy
          show projectStore ρ_hoist.store ρ_h'.store y ≠ none
          unfold projectStore
          have h_parent_some : (ρ_hoist.store y).isSome := by
            cases h : ρ_hoist.store y with
            | none => exact absurd h (h_hoist_bound y hy)
            | some _ => simp
          rw [h_parent_some]; exact h_bound_inner y hy
  | .ite g tss ess md =>
    subst h_match
    -- === Decompose the §E preconditions for `[.ite g tss ess md]` to the
    --     branches `tss` (processed at σ) and `ess` (processed at σ1). ===
    have h_iv_split : Block.initVars [Stmt.ite g tss ess md] =
        Block.initVars tss ++ Block.initVars ess := by
      simp only [Block.initVars, Stmt.initVars, List.append_nil]
    have h_mod_split : Block.modifiedVars [Stmt.ite g tss ess md] =
        Block.modifiedVars tss ++ Block.modifiedVars ess := by
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil]
    -- Bool preconds.
    have h_nd_branches : Block.containsNondetLoop tss = false ∧ Block.containsNondetLoop ess = false := by
      simp only [Stmt.containsNondetLoop,
        Bool.or_eq_false_iff] at h_no_nd; exact h_no_nd
    have h_fd_branches : Block.containsFuncDecl tss = false ∧ Block.containsFuncDecl ess = false := by
      simp only [Stmt.containsFuncDecl,
        Bool.or_eq_false_iff] at h_no_fd; exact h_no_fd
    have h_inv_branches : Block.loopHasNoInvariants tss = true ∧ Block.loopHasNoInvariants ess = true := by
      simp only [Stmt.loopHasNoInvariants,
        Bool.and_eq_true] at h_no_inv; exact h_no_inv
    have h_measure_branches : Block.loopMeasureNone tss = true ∧ Block.loopMeasureNone ess = true := by
      simp only [Stmt.loopMeasureNone,
        Bool.and_eq_true] at h_no_measure; exact h_no_measure
    have h_exprs_shapefree_branches :
        Block.exprsShapeFree (P := P) Q tss ∧
          Block.exprsShapeFree (P := P) Q ess := by
      have h := h_exprs_shapefree
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree] at h
      exact ⟨h.1.2.1, h.1.2.2⟩
    -- uniqueInits: Nodup splits over the append.
    have h_unique_full : (Block.initVars tss ++ Block.initVars ess).Nodup := by
      have : Block.uniqueInits [Stmt.ite g tss ess md] =
          (Block.initVars [Stmt.ite g tss ess md]).Nodup := rfl
      rw [this, h_iv_split] at h_unique; exact h_unique
    have h_unique_tss : Block.uniqueInits tss := (List.nodup_append.mp h_unique_full).1
    have h_unique_ess : Block.uniqueInits ess := (List.nodup_append.mp h_unique_full).2.1
    -- hoistedNamesFreshInRhsAndGuards: split into the two branches.
    have h_fresh_unfold := h_fresh
    unfold Block.hoistedNamesFreshInRhsAndGuards at h_fresh_unfold
    rw [Bool.and_eq_true] at h_fresh_unfold
    obtain ⟨h_guards_full, h_namesFresh_full⟩ := h_fresh_unfold
    -- guards: `[.ite g tss ess md]` guards split into tss guards + ess guards
    -- (the `.ite` guard expression's freshness lives in `namesFreshInExprs`).
    simp only [Block.hoistedNamesFreshInGuards, Stmt.hoistedNamesFreshInGuards,
      Bool.and_true, Bool.and_eq_true] at h_guards_full
    obtain ⟨h_guards_tss, h_guards_ess⟩ := h_guards_full
    have h_guards_tss_block : Block.hoistedNamesFreshInGuards tss = true := h_guards_tss
    have h_guards_ess_block : Block.hoistedNamesFreshInGuards ess = true := h_guards_ess
    -- namesFreshInRhsExprs over initVars [.ite ..]: split via subset + the ite arm
    -- (the `.ite` guard read position is no longer checked, so no guard conjunct).
    have h_sub_tss : (Block.initVars tss : List P.Ident) ⊆ Block.initVars [Stmt.ite g tss ess md] := by
      rw [h_iv_split]; exact fun _ h => List.mem_append.mpr (Or.inl h)
    have h_sub_ess : (Block.initVars ess : List P.Ident) ⊆ Block.initVars [Stmt.ite g tss ess md] := by
      rw [h_iv_split]; exact fun _ h => List.mem_append.mpr (Or.inr h)
    simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true,
      Bool.and_eq_true] at h_namesFresh_full
    obtain ⟨h_nf_tss_iv, h_nf_ess_iv⟩ := h_namesFresh_full
    have h_fresh_tss : Block.hoistedNamesFreshInRhsAndGuards (P := P) tss = true := by
      unfold Block.hoistedNamesFreshInRhsAndGuards
      rw [Bool.and_eq_true]
      exact ⟨h_guards_tss_block, Block.namesFreshInRhsExprs_subset h_sub_tss tss h_nf_tss_iv⟩
    have h_fresh_ess : Block.hoistedNamesFreshInRhsAndGuards (P := P) ess = true := by
      unfold Block.hoistedNamesFreshInRhsAndGuards
      rw [Bool.and_eq_true]
      exact ⟨h_guards_ess_block, Block.namesFreshInRhsExprs_subset h_sub_ess ess h_nf_ess_iv⟩
    -- namesFreshInExprs A / B split over the branches.
    have h_names_fresh_A_split :
        Block.namesFreshInExprs A tss = true ∧ Block.namesFreshInExprs A ess = true := by
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        Bool.and_eq_true] at h_names_fresh; exact ⟨h_names_fresh.1.2, h_names_fresh.2⟩
    have h_names_fresh_B_split :
        Block.namesFreshInExprs B tss = true ∧ Block.namesFreshInExprs B ess = true := by
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        Bool.and_eq_true] at h_names_fresh_B; exact ⟨h_names_fresh_B.1.2, h_names_fresh_B.2⟩
    -- initVars-based disjointness / undef: split via initVars membership.
    have h_lhs_disjoint_tss : ∀ y ∈ Block.initVars tss, y ∉ A := fun y hy =>
      h_lhs_disjoint y (h_sub_tss hy)
    have h_lhs_disjoint_ess : ∀ y ∈ Block.initVars ess, y ∉ A := fun y hy =>
      h_lhs_disjoint y (h_sub_ess hy)
    have h_extra_disjoint_tss : ∀ y ∈ Block.initVars tss, y ∉ B := fun y hy =>
      h_extra_disjoint y (h_sub_tss hy)
    have h_extra_disjoint_ess : ∀ y ∈ Block.initVars ess, y ∉ B := fun y hy =>
      h_extra_disjoint y (h_sub_ess hy)
    have h_mod_sub_tss : (Block.modifiedVars tss : List P.Ident) ⊆
        Block.modifiedVars [Stmt.ite g tss ess md] := by
      rw [h_mod_split]; exact fun _ h => List.mem_append.mpr (Or.inl h)
    have h_mod_sub_ess : (Block.modifiedVars ess : List P.Ident) ⊆
        Block.modifiedVars [Stmt.ite g tss ess md] := by
      rw [h_mod_split]; exact fun _ h => List.mem_append.mpr (Or.inr h)
    have h_mod_disjoint_A_tss : ∀ x ∈ Block.modifiedVars tss, x ∉ A := fun x hx =>
      h_mod_disjoint_A x (h_mod_sub_tss hx)
    have h_mod_disjoint_A_ess : ∀ x ∈ Block.modifiedVars ess, x ∉ A := fun x hx =>
      h_mod_disjoint_A x (h_mod_sub_ess hx)
    have h_mod_disjoint_B_tss : ∀ x ∈ Block.modifiedVars tss, x ∉ B := fun x hx =>
      h_mod_disjoint_B x (h_mod_sub_tss hx)
    have h_mod_disjoint_B_ess : ∀ x ∈ Block.modifiedVars ess, x ∉ B := fun x hx =>
      h_mod_disjoint_B x (h_mod_sub_ess hx)
    have h_hoist_undef_tss : ∀ y ∈ Block.initVars tss, ρ_src.store y = none := fun y hy =>
      h_hoist_undef y (h_sub_tss hy)
    have h_hoist_undef_ess : ∀ y ∈ Block.initVars ess, ρ_src.store y = none := fun y hy =>
      h_hoist_undef y (h_sub_ess hy)
    have h_hoist_undef_h_tss : ∀ y ∈ Block.initVars tss, ρ_hoist.store y = none := fun y hy =>
      h_hoist_undef_h y (h_sub_tss hy)
    have h_hoist_undef_h_ess : ∀ y ∈ Block.initVars ess, ρ_hoist.store y = none := fun y hy =>
      h_hoist_undef_h y (h_sub_ess hy)
    -- σ-freshness / shape-free restricted to each branch.
    have h_src_fresh_tss :
        ∀ str ∈ StringGenState.stringGens σ,
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
      intro str hstr
      obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
      exact ⟨hA, hB, fun h => hiv (h_sub_tss h)⟩
    have h_src_shapefree_tss :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars tss ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars tss := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (h_sub_tss h), fun h => hmv (h_mod_sub_tss h)⟩
    have h_src_shapefree_ess :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars ess ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars ess := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (h_sub_ess h), fun h => hmv (h_mod_sub_ess h)⟩
    -- GenStep facts: σ → σ1 = (Block.hoistLoopPrefixInitsM tss σ).2; WF of σ1.
    have h_genStep_tss : StringGenState.GenStep σ (Block.hoistLoopPrefixInitsM tss σ).2 :=
      Block.hoistLoopPrefixInitsM_genStep tss σ
    have h_wf_σ1 : StringGenState.WF (Block.hoistLoopPrefixInitsM tss σ).2 :=
      h_genStep_tss.wf_mono h_wf_σ
    -- σ-freshness for ESS at σ1: thread via SrcNamesFreshFromGen.genStep_of_delta.
    have h_src_fresh_ess_σ1 :
        ∀ str ∈ StringGenState.stringGens (Block.hoistLoopPrefixInitsM tss σ).2,
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
      have h_fresh_σ_ess : SrcNamesFreshFromGen (P := P) A B (Block.initVars ess) σ := by
        intro str hstr
        obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
        exact ⟨hA, hB, fun h => hiv (h_sub_ess h)⟩
      exact SrcNamesFreshFromGen.genStep_of_delta
        (Block.hoistLoopPrefixInitsM_genStep_delta_Q hQmint tss σ)
        (fun str hsuf => let ⟨a, b, c, _⟩ := h_src_shapefree_ess str hsuf; ⟨a, b, c⟩) h_fresh_σ_ess
    -- Store-shapefree at σ1 for the ELSE branch.  The else branch runs from the
    -- SAME entry stores `ρ_src`/`ρ_hoist` (the `.ite` selects one branch), so the
    -- store facts are unchanged; only the generator state index advances to σ1.
    -- A suffix name `∉ stringGens σ1` is `∉ stringGens σ` by genStep monotonicity,
    -- so the σ-version facts transfer.
    have h_src_store_shapefree_σ1 : ∀ str : String, Q str →
        str ∉ StringGenState.stringGens (Block.hoistLoopPrefixInitsM tss σ).2 →
        ρ_src.store (HasIdent.ident (P := P) str) = none := fun str h_suf h_notσ1 =>
      h_src_store_shapefree str h_suf (fun h => h_notσ1 (h_genStep_tss.subset h))
    have h_hoist_store_shapefree_σ1 : ∀ str : String, Q str →
        str ∉ StringGenState.stringGens (Block.hoistLoopPrefixInitsM tss σ).2 →
        ρ_hoist.store (HasIdent.ident (P := P) str) = none := fun str h_suf h_notσ1 =>
      h_hoist_store_shapefree str h_suf (fun h => h_notσ1 (h_genStep_tss.subset h))
    -- === Rewrite the residual to the singleton hoisted `.ite`. ===
    have h_ite_out :
        (Stmt.hoistLoopPrefixInitsM (.ite g tss ess md) σ).1 =
          [Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
            (Block.hoistLoopPrefixInitsM ess
              (Block.hoistLoopPrefixInitsM tss σ).2).1 md] :=
      Stmt.hoistLoopPrefixInitsM_ite_out g tss ess md σ
    rw [h_ite_out]
    -- === Branch glue: given the single hoisted ite step into `branch_residual`
    --     and the branch's §E outcome, drive the singleton `.ite` to completion.
    --     `ite_stmt` is the hoisted `.ite` (then-residual at σ, else at σ1). ===
    have branch_glue :
        ∀ (ite_stmt : Stmt P (Cmd P)) (branch_residual : List (Stmt P (Cmd P)))
          {ρ_h' : Env P} {cfg_b cfg_hoist : Config P (Cmd P)},
          StepStmt P (EvalCmd P) extendEval
            (.stmt ite_stmt ρ_hoist)
            (.stmts branch_residual ρ_hoist) →
          StepStmtStar P (EvalCmd P) extendEval (.stmts branch_residual ρ_hoist) cfg_hoist →
          ((∃ r, cfg_b = .terminal r ∧ cfg_hoist = .terminal ρ_h' ∧
              HoistInv (P := P) A B subst r.store ρ_h'.store ∧
              r.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
           (∃ l r, cfg_b = .exiting l r ∧ cfg_hoist = .exiting l ρ_h' ∧
              HoistInv (P := P) A B subst r.store ρ_h'.store ∧
              r.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))) →
          ∃ ρ_h'2, ∃ cfg_hoist2 : Config P (Cmd P),
            StepStmtStar P (EvalCmd P) extendEval
              (.stmts [ite_stmt] ρ_hoist) cfg_hoist2
            ∧ ((∃ ρ_src' : Env P, cfg_b = .terminal ρ_src' ∧ cfg_hoist2 = .terminal ρ_h'2 ∧
                  HoistInv (P := P) A B subst ρ_src'.store ρ_h'2.store ∧
                  ρ_src'.hasFailure = ρ_h'2.hasFailure ∧ (∀ y ∈ B, ρ_h'2.store y ≠ none)) ∨
               (∃ lbl ρ_src', cfg_b = .exiting lbl ρ_src' ∧ cfg_hoist2 = .exiting lbl ρ_h'2 ∧
                  HoistInv (P := P) A B subst ρ_src'.store ρ_h'2.store ∧
                  ρ_src'.hasFailure = ρ_h'2.hasFailure ∧ (∀ y ∈ B, ρ_h'2.store y ≠ none))) := by
      intro ite_stmt branch_residual ρ_h' cfg_b cfg_hoist h_step_hoist h_branch_hoist h_outcome
      rcases h_outcome with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1, hr2, hr3, hr4, hr5⟩
      · -- branch terminal.
        subst hr2
        refine ⟨ρ_h', .terminal ρ_h', ?_, Or.inl ⟨r, hr1, rfl, hr3, hr4, hr5⟩⟩
        refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
        refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner h_step_hoist) ?_
        refine ReflTrans_Transitive _ _ _ _
          (seq_inner_star P (EvalCmd P) extendEval _ _ [] h_branch_hoist) ?_
        refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
        exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (.refl _)
      · -- branch exiting.
        subst hr2
        refine ⟨ρ_h', .exiting l ρ_h', ?_, Or.inr ⟨l, r, hr1, rfl, hr3, hr4, hr5⟩⟩
        refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
        refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner h_step_hoist) ?_
        refine ReflTrans_Transitive _ _ _ _
          (seq_inner_star P (EvalCmd P) extendEval _ _ [] h_branch_hoist) ?_
        exact ReflTrans.step _ _ _ StepStmt.step_seq_exit (.refl _)
    -- The hoisted `.ite` to drive (then-residual at σ, else-residual at σ1):
    -- The §E conclusion shape for the singleton hoisted `.ite` (used as the
    -- explicit return type of the per-branch drivers).
    let IteGoal : Prop :=
      ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
        StepStmtStar P (EvalCmd P) extendEval
          (.stmts [Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
            (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).1 md] ρ_hoist)
          cfg_hoist
        ∧ ((∃ ρ_src' : Env P, cfg_src = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
              HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
              ρ_src'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
           (∃ lbl ρ_src', cfg_src = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
              HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
              ρ_src'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)))
    -- THEN-branch driver: recurse the §E Block-IH on `tss` at σ.
    have run_then :
        StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ_src) cfg_src →
        StepStmt P (EvalCmd P) extendEval
          (.stmt (Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
            (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).1 md) ρ_hoist)
          (.stmts (Block.hoistLoopPrefixInitsM tss σ).1 ρ_hoist) →
        IteGoal := by
      intro hr1 h_step
      obtain ⟨ρ_h', cfg_hoist, h_branch_hoist, h_outcome⟩ :=
        Block.hoistLoopPrefixInits_preserves hQmint A B subst tss σ
          h_nd_branches.1 h_fd_branches.1 h_inv_branches.1 h_measure_branches.1
          h_exprs_shapefree_branches.1
          h_unique_tss h_fresh_tss h_names_fresh_A_split.1 h_names_fresh_B_split.1
          h_lhs_disjoint_tss h_extra_disjoint_tss h_mod_disjoint_A_tss h_mod_disjoint_B_tss
          h_hoist_undef_tss h_hoist_undef_h_tss
          h_src_store_shapefree h_hoist_store_shapefree
          h_wf_σ h_src_fresh_tss h_src_shapefree_tss h_subst_wf h_hinv h_eval_eq h_hf_eq
          h_hoist_bound hr1 h_cfg_src h_wfvar h_wfcongr h_wfsubst h_wfdef
      exact branch_glue _ (Block.hoistLoopPrefixInitsM tss σ).1 h_step h_branch_hoist h_outcome
    -- ELSE-branch driver: recurse the §E Block-IH on `ess` at σ1.
    have run_else :
        StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ_src) cfg_src →
        StepStmt P (EvalCmd P) extendEval
          (.stmt (Stmt.ite g (Block.hoistLoopPrefixInitsM tss σ).1
            (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).1 md) ρ_hoist)
          (.stmts (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).1 ρ_hoist) →
        IteGoal := by
      intro hr1 h_step
      obtain ⟨ρ_h', cfg_hoist, h_branch_hoist, h_outcome⟩ :=
        Block.hoistLoopPrefixInits_preserves hQmint A B subst ess (Block.hoistLoopPrefixInitsM tss σ).2
          h_nd_branches.2 h_fd_branches.2 h_inv_branches.2 h_measure_branches.2
          h_exprs_shapefree_branches.2
          h_unique_ess h_fresh_ess h_names_fresh_A_split.2 h_names_fresh_B_split.2
          h_lhs_disjoint_ess h_extra_disjoint_ess h_mod_disjoint_A_ess h_mod_disjoint_B_ess
          h_hoist_undef_ess h_hoist_undef_h_ess
          h_src_store_shapefree_σ1 h_hoist_store_shapefree_σ1
          h_wf_σ1 h_src_fresh_ess_σ1 h_src_shapefree_ess h_subst_wf h_hinv h_eval_eq h_hf_eq
          h_hoist_bound hr1 h_cfg_src h_wfvar h_wfcongr h_wfsubst h_wfdef
      exact branch_glue _ (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).1
        h_step h_branch_hoist h_outcome
    -- === Invert the SOURCE run: `.stmt (.ite g tss ess md) ρ_src` takes one step
    --     selecting a branch, then the branch runs. ===
    cases h_run_src with
    | refl => rcases h_cfg_src with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact nomatch h
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_true h_eval h_wfb =>
        have h_guard := h_eval
        rw [ite_guard_agree (subst := subst) (tss := tss) (ess := ess) (md := md)
          h_names_fresh h_names_fresh_B h_hinv
          (read_vars_def_of_eval (h_wfdef ρ_src) h_eval) h_eval_eq h_wfcongr] at h_guard
        rw [h_eval_eq] at h_wfb
        exact run_then hr1 (StepStmt.step_ite_true h_guard h_wfb)
      | step_ite_false h_eval h_wfb =>
        have h_guard := h_eval
        rw [ite_guard_agree (subst := subst) (tss := tss) (ess := ess) (md := md)
          h_names_fresh h_names_fresh_B h_hinv
          (read_vars_def_of_eval (h_wfdef ρ_src) h_eval) h_eval_eq h_wfcongr] at h_guard
        rw [h_eval_eq] at h_wfb
        exact run_else hr1 (StepStmt.step_ite_false h_guard h_wfb)
      | step_ite_nondet_true => exact run_then hr1 StepStmt.step_ite_nondet_true
      | step_ite_nondet_false => exact run_else hr1 StepStmt.step_ite_nondet_false
  | .loop g m inv body md =>
    subst h_match
    -- === A. Normalize the loop shape: g = .det g', m = none, inv = []. ===
    -- `loopMeasureNone` ⇒ `m = none`; `loopHasNoInvariants` ⇒ `inv = []`;
    -- `containsNondetLoop = false` ⇒ guard is `.det g'`.
    have h_no_measure_s : Stmt.loopMeasureNone (Stmt.loop g m inv body md) = true := by
      simpa only [Block.loopMeasureNone, Bool.and_true] using h_no_measure
    have h_no_inv_s : Stmt.loopHasNoInvariants (Stmt.loop g m inv body md) = true := by
      simpa only [Block.loopHasNoInvariants, Bool.and_true] using h_no_inv
    have h_no_nd_s : Stmt.containsNondetLoop (Stmt.loop g m inv body md) = false := by
      simpa only [Block.containsNondetLoop, Bool.or_false] using h_no_nd
    have h_m_none : m = none := by
      rw [Stmt.loopMeasureNone, Bool.and_eq_true] at h_no_measure_s
      exact Option.isNone_iff_eq_none.mp h_no_measure_s.1
    have h_inv_nil : inv = [] := by
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_no_inv_s
      exact List.isEmpty_iff.mp h_no_inv_s.1
    subst h_m_none; subst h_inv_nil
    have h_body_nd : ∃ g', g = ExprOrNondet.det g' ∧ Block.containsNondetLoop body = false := by
      cases g with
      | nondet => rw [Stmt.containsNondetLoop] at h_no_nd_s; exact absurd h_no_nd_s (by simp)
      | det g' => refine ⟨g', rfl, ?_⟩; rw [Stmt.containsNondetLoop] at h_no_nd_s; exact h_no_nd_s
    obtain ⟨g', rfl, h_nd_body⟩ := h_body_nd
    -- === Carrier identities: initVars/modifiedVars of the singleton loop ARE body's. ===
    have h_iv_body : Block.initVars [Stmt.loop (.det g') none [] body md] = Block.initVars body := by
      simp only [Block.initVars, Stmt.initVars, List.append_nil]
    have h_mod_body : Block.modifiedVars [Stmt.loop (.det g') none [] body md] = Block.modifiedVars body := by
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil]
    -- === Body-level §E preconditions, decomposed from the loop's. ===
    have h_fd_body : Block.containsFuncDecl body = false := by
      have : Stmt.containsFuncDecl (Stmt.loop (.det g') none [] body md) = false := by
        simpa only [Block.containsFuncDecl, Bool.or_false] using h_no_fd
      rw [Stmt.containsFuncDecl] at this; exact this
    have h_inv_body : Block.loopHasNoInvariants body = true := by
      rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_no_inv_s; exact h_no_inv_s.2
    have h_measure_body : Block.loopMeasureNone body = true := by
      rw [Stmt.loopMeasureNone, Bool.and_eq_true] at h_no_measure_s; exact h_no_measure_s.2
    have h_exprs_shapefree_body : Block.exprsShapeFree (P := P) Q body := by
      have h := h_exprs_shapefree
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree] at h
      exact h.1.2.2.2
    have h_unique_body : Block.uniqueInits body := by
      show (Block.initVars body).Nodup; rw [← h_iv_body]; exact h_unique
    have h_fresh_body : Block.hoistedNamesFreshInRhsAndGuards (P := P) body = true := by
      have h := h_fresh
      unfold Block.hoistedNamesFreshInRhsAndGuards at h ⊢
      rw [h_iv_body] at h
      rw [Bool.and_eq_true] at h ⊢
      obtain ⟨h_guards, h_names⟩ := h
      refine ⟨?_, ?_⟩
      · simp only [Block.hoistedNamesFreshInGuards, Stmt.hoistedNamesFreshInGuards,
          Bool.and_true, Bool.and_eq_true] at h_guards; exact h_guards.2
      · -- the `.loop` arm of `namesFreshInRhsExprs` recurses into the body only.
        simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
          Bool.and_true] at h_names
        exact h_names
    have h_names_fresh_A_body : Block.namesFreshInExprs A body = true := by
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        Bool.and_eq_true] at h_names_fresh; exact h_names_fresh.2
    have h_names_fresh_B_body : Block.namesFreshInExprs B body = true := by
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true,
        Bool.and_eq_true] at h_names_fresh_B; exact h_names_fresh_B.2
    -- guard `g'` freshness from A / B.
    have freshFromIdents_notmem : ∀ {z : P.Ident} {vars : List P.Ident},
        freshFromIdents z vars = true → z ∉ vars := by
      intro z vars h
      unfold freshFromIdents at h
      rw [List.all_eq_true] at h
      intro hmem
      have h_z := h z hmem
      have h_eq : (P.EqIdent z z).decide = true := by simp
      rw [h_eq] at h_z
      exact absurd h_z (by decide)
    have h_g_A_fresh : ∀ x ∈ A, x ∉ HasVarsPure.getVars g' := by
      simp only [Block.namesFreshInExprs, Bool.and_true] at h_names_fresh
      unfold Stmt.namesFreshInExprs at h_names_fresh
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h_names_fresh
      obtain ⟨⟨⟨h_g, _⟩, _⟩, _⟩ := h_names_fresh
      rw [List.all_eq_true] at h_g
      intro x hx
      have := h_g x hx
      rw [ExprOrNondet.getVars] at this
      exact freshFromIdents_notmem this
    have h_g_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars g' := by
      simp only [Block.namesFreshInExprs, Bool.and_true] at h_names_fresh_B
      unfold Stmt.namesFreshInExprs at h_names_fresh_B
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h_names_fresh_B
      obtain ⟨⟨⟨h_g, _⟩, _⟩, _⟩ := h_names_fresh_B
      rw [List.all_eq_true] at h_g
      intro x hx
      have := h_g x hx
      rw [ExprOrNondet.getVars] at this
      exact freshFromIdents_notmem this
    -- initVars/modifiedVars-based disjointness + undef + σ-freshness for body.
    have h_lhs_disjoint_body : ∀ y ∈ Block.initVars body, y ∉ A := fun y hy =>
      h_lhs_disjoint y (by rw [h_iv_body]; exact hy)
    have h_extra_disjoint_body : ∀ y ∈ Block.initVars body, y ∉ B := fun y hy =>
      h_extra_disjoint y (by rw [h_iv_body]; exact hy)
    have h_mod_disjoint_A_body : ∀ x ∈ Block.modifiedVars body, x ∉ A := fun x hx =>
      h_mod_disjoint_A x (by rw [h_mod_body]; exact hx)
    have h_mod_disjoint_B_body : ∀ x ∈ Block.modifiedVars body, x ∉ B := fun x hx =>
      h_mod_disjoint_B x (by rw [h_mod_body]; exact hx)
    have h_hoist_undef_body : ∀ y ∈ Block.initVars body, ρ_src.store y = none := fun y hy =>
      h_hoist_undef y (by rw [h_iv_body]; exact hy)
    have h_hoist_undef_h_body : ∀ y ∈ Block.initVars body, ρ_hoist.store y = none := fun y hy =>
      h_hoist_undef_h y (by rw [h_iv_body]; exact hy)
    have h_src_fresh_body :
        ∀ str ∈ StringGenState.stringGens σ,
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
      intro str hstr
      obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
      exact ⟨hA, hB, fun h => hiv (by rw [h_iv_body]; exact h)⟩
    have h_src_shapefree_body :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧ HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars body ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars body := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (by rw [h_iv_body]; exact h),
        fun h => hmv (by rw [h_mod_body]; exact h)⟩
    -- === Loop output decomposition: havocs ++ [.loop g' none [] body₃ md]. ===
    -- body₁ = post-order hoist of body; σ₁ = its final gen state; E = harvest of
    -- body₁ at σ₁; body₃ = applyRenames (substOf' E) body₂ where body₂ is the
    -- lift residual.  The output's renames equal substOf' E (entries_from_lift).
    -- Abbreviations (no `set` tactic in this project): the post-order body, its
    -- gen state, the harvest, and the rewritten loop body.
    let body₁ : List (Stmt P (Cmd P)) := (Block.hoistLoopPrefixInitsM body σ).1
    let σ₁ : StringGenState := (Block.hoistLoopPrefixInitsM body σ).2
    let E : List (LoopInitHoistLoopDriver.Entry P) :=
      LoopInitHoistLoopDriver.Block.entriesOf body₁ σ₁
    let body₃ : List (Stmt P (Cmd P)) :=
      Block.applyRenames (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.1
        (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.2
    -- The hoisted loop residual.
    have h_loop_out :
        (Stmt.hoistLoopPrefixInitsM (Stmt.loop (.det g') none [] body md) σ).1 =
          (Block.liftInitsInLoopBodyM body₁ σ₁).1.1.map Stmt.cmd ++
          [Stmt.loop (.det g') none [] body₃ md] :=
      Stmt.hoistLoopPrefixInitsM_loop_out (.det g') none [] body md σ
    rw [h_loop_out]
    -- The havocs (mapped to .cmd) equal havocStmts' E; renames equal substOf' E.
    have h_harvest := LoopInitHoistLoopDriver.Block.lift_harvest_subst body₁ σ₁
    have h_havoc_eq : (Block.liftInitsInLoopBodyM body₁ σ₁).1.1.map Stmt.cmd =
        LoopInitHoistLoopDriver.havocStmts' E := h_harvest.1
    have h_renames_eq : (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.1 =
        LoopInitHoistLoopDriver.substOf' E := h_harvest.2
    rw [h_havoc_eq]
    -- === Step A: the §E Block IH at the harvest `σ`, presented in the raw
    --     ∀-shape `loop_arm_close` expects (both source- and hoist-side
    --     `σ`-relative store-shape-freedom supplied directly per iteration). ===
    have stepA : ∀ (ρ_s ρ_h : Env P),
        HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
        ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
        (∀ y ∈ B, ρ_h.store y ≠ none) →
        (∀ y ∈ Block.initVars body, ρ_s.store y = none) →
        (∀ y ∈ Block.initVars body, ρ_h.store y = none) →
        (∀ str : String, Q str →
           str ∉ StringGenState.stringGens σ → ρ_s.store (HasIdent.ident (P := P) str) = none) →
        (∀ str : String, Q str →
           str ∉ StringGenState.stringGens σ → ρ_h.store (HasIdent.ident (P := P) str) = none) →
        ∀ (ρ_s' : Env P),
          StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ_s) (.terminal ρ_s') →
          ∃ ρ_h' : Env P,
            StepStmtStar P (EvalCmd P) extendEval (.stmts body₁ ρ_h) (.terminal ρ_h') ∧
            HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
            ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
      intro ρ_s ρ_h h_hinv_i h_eval_i h_hf_i h_bnd_i h_Vs_i h_Vh_i h_src_sf_i h_hoist_sf_i ρ_s' h_run_i
      obtain ⟨ρ_h', cfg_h, h_run_h, h_out⟩ :=
        Block.hoistLoopPrefixInits_preserves hQmint A B subst body σ
          h_nd_body h_fd_body h_inv_body h_measure_body
          h_exprs_shapefree_body h_unique_body h_fresh_body
          h_names_fresh_A_body h_names_fresh_B_body
          h_lhs_disjoint_body h_extra_disjoint_body h_mod_disjoint_A_body h_mod_disjoint_B_body
          (fun y hy => h_Vs_i y hy) (fun y hy => h_Vh_i y hy)
          h_src_sf_i h_hoist_sf_i
          h_wf_σ h_src_fresh_body h_src_shapefree_body h_subst_wf h_hinv_i h_eval_i h_hf_i h_bnd_i
          h_run_i (Or.inl ⟨ρ_s', rfl⟩)
          h_wfvar h_wfcongr h_wfsubst h_wfdef
      rcases h_out with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1, _, _, _, _⟩
      · cases hr1; cases hr2
        exact ⟨ρ_h', h_run_h, hr3, hr4, hr5⟩
      · exact absurd hr1 (by rintro ⟨⟩)
    -- === Step A (exiting): the §E Block IH at the harvest `σ`, presented in the
    --     raw ∀-shape `loop_arm_close` expects for a body iteration that BREAKS
    --     with a label.  Same Block IH, dispatched with the `.exiting` `cfg_src`
    --     disjunct; the `.terminal` output clause is impossible (`cfg_src` is
    --     `.exiting`).  A body `.exit` is admitted (no static no-exit guard is consumed). ===
    have stepA_exit : ∀ (ρ_s ρ_h : Env P),
        HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
        ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
        (∀ y ∈ B, ρ_h.store y ≠ none) →
        (∀ y ∈ Block.initVars body, ρ_s.store y = none) →
        (∀ y ∈ Block.initVars body, ρ_h.store y = none) →
        (∀ str : String, Q str →
           str ∉ StringGenState.stringGens σ → ρ_s.store (HasIdent.ident (P := P) str) = none) →
        (∀ str : String, Q str →
           str ∉ StringGenState.stringGens σ → ρ_h.store (HasIdent.ident (P := P) str) = none) →
        ∀ (l : String) (ρ_s' : Env P),
          StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ_s) (.exiting l ρ_s') →
          ∃ ρ_h' : Env P,
            StepStmtStar P (EvalCmd P) extendEval (.stmts body₁ ρ_h) (.exiting l ρ_h') ∧
            HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
            ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) := by
      intro ρ_s ρ_h h_hinv_i h_eval_i h_hf_i h_bnd_i h_Vs_i h_Vh_i h_src_sf_i h_hoist_sf_i l ρ_s' h_run_i
      obtain ⟨ρ_h', cfg_h, h_run_h, h_out⟩ :=
        Block.hoistLoopPrefixInits_preserves hQmint A B subst body σ
          h_nd_body h_fd_body h_inv_body h_measure_body
          h_exprs_shapefree_body h_unique_body h_fresh_body
          h_names_fresh_A_body h_names_fresh_B_body
          h_lhs_disjoint_body h_extra_disjoint_body h_mod_disjoint_A_body h_mod_disjoint_B_body
          (fun y hy => h_Vs_i y hy) (fun y hy => h_Vh_i y hy)
          h_src_sf_i h_hoist_sf_i
          h_wf_σ h_src_fresh_body h_src_shapefree_body h_subst_wf h_hinv_i h_eval_i h_hf_i h_bnd_i
          h_run_i (Or.inr ⟨l, ρ_s', rfl⟩)
          h_wfvar h_wfcongr h_wfsubst h_wfdef
      rcases h_out with ⟨r, hr1, _, _, _, _⟩ | ⟨l', r, hr1, hr2, hr3, hr4, hr5⟩
      · exact absurd hr1 (by rintro ⟨⟩)
      · obtain ⟨hl_eq, hr_eq⟩ : l' = l ∧ r = ρ_s' := by
          cases hr1; exact ⟨rfl, rfl⟩
        cases hl_eq; cases hr_eq; cases hr2
        exact ⟨ρ_h', h_run_h, hr3, hr4, hr5⟩
    -- === Step B: the lift renaming simulation at `body₁`'s own harvest carriers. ===
    have h_src_shapefree_body_iv : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body := fun str h_suf =>
      (h_src_shapefree_body str h_suf).2.2.1
    -- Source-side modifiedVars-shape-freedom, projected from the threaded
    -- 4-conjunct `h_src_shapefree_body`: a `Q`-kind string never names a
    -- source set-target.
    have h_mod_shapefree_body : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.modifiedVars body := fun str h_suf =>
      (h_src_shapefree_body str h_suf).2.2.2
    -- `targetsOf' E` are minted in the lift σ₁ → σ₂ (so ∉ stringGens σ₁) and are
    -- `_<digit>`-suffix-shaped.  `modifiedVars body₁` splits (by the post-order
    -- pass's `modifiedVars` classification) into: ORIGINAL `.set` targets (members
    -- of `modifiedVars body ++ initVars body`, suffix-free for a well-formed
    -- source) and FRESH names from NESTED-loop init lifting (∈ stringGens σ₁).
    -- Both classes are disjoint from the suffix-shaped, ∉-σ₁ targets.
    have h_mod_disjoint_B1 : ∀ x ∈ Block.modifiedVars body₁,
        x ∉ LoopInitHoistLoopDriver.targetsOf' E :=
      LoopInitHoistLoopArmWF.Block.modifiedVars_disjoint_targetsOf'_self hQmint body σ h_wf_σ
        h_unique_body h_src_shapefree_body_iv h_mod_shapefree_body
    -- `body₃` (arm-local) uses the lift's OWN renames `(lift body₁ σ₁).1.2.1`,
    -- whereas `stepB_self_of_lift` produces `body₃` over `substOf' E`; the two
    -- coincide by the harvest identity `h_renames_eq`.
    have stepB : LoopInitHoistLoopDriver.BodySimSum (extendEval := extendEval)
        (LoopInitHoistLoopDriver.sourcesOf' E) (LoopInitHoistLoopDriver.targetsOf' E)
        (LoopInitHoistLoopDriver.substOf' E) body₁ body₃ := by
      have hB :=
        LoopInitHoistLoopArmWF.Block.stepB_self_of_lift hQmint (extendEval := extendEval) body σ h_wf_σ
          h_nd_body h_fd_body h_inv_body h_measure_body h_unique_body
          h_exprs_shapefree_body h_src_shapefree_body_iv h_mod_disjoint_B1
          h_wfvar h_wfcongr h_wfsubst h_wfdef
      show LoopInitHoistLoopDriver.BodySimSum (extendEval := extendEval)
        (LoopInitHoistLoopDriver.sourcesOf' E) (LoopInitHoistLoopDriver.targetsOf' E)
        (LoopInitHoistLoopDriver.substOf' E) body₁
        (Block.applyRenames (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.1
          (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.2)
      rw [h_renames_eq]
      exact hB
    -- === Assemble the close.  Abbreviations for the harvest carriers. ===
    have h_wf_σ₁ : StringGenState.WF σ₁ :=
      (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf_σ
    -- Sources ⊆ initVars body₁; targets are `_<digit>`-suffixed and ∉ σ₁.
    -- Source-side classification: each harvested source is ORIGINAL (∈ initVars
    -- body) or FRESH (= ident str, `Q str`, ∈ σ₁ \ σ).
    have h_src_class : ∀ a ∈ LoopInitHoistLoopDriver.sourcesOf' E,
        (a ∈ Block.initVars body) ∨
        (∃ str : String, a = HasIdent.ident str ∧ Q str ∧
          str ∈ StringGenState.stringGens σ₁ ∧ str ∉ StringGenState.stringGens σ) := by
      intro a ha
      have h_a_in₁ : a ∈ Block.initVars body₁ :=
        LoopInitHoistLoopDriver.Block.sourcesOf_entriesOf_subset body₁ σ₁ a ha
      have h_class :=
        (LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_initVars_classified hQmint body σ
          h_wf_σ h_unique_body h_src_shapefree_body_iv).1 a h_a_in₁
      rcases h_class with h_o | ⟨str, he, hin, hnot, hQ⟩
      · exact Or.inl h_o
      · exact Or.inr ⟨str, he, hQ, hin, hnot⟩
    -- Each harvested target is `ident str` with `Q str` and ∉ σ₁ ⊇ σ.
    have h_tgt_class : ∀ b ∈ LoopInitHoistLoopDriver.targetsOf' E,
        ∃ str : String, b = HasIdent.ident str ∧ Q str ∧
          str ∉ StringGenState.stringGens σ₁ := by
      intro b hb
      obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hb
      obtain ⟨str, h_b_eq, _, h_notσ₁⟩ :=
        (LoopInitHoistLoopArmWF.Block.entriesOf_targetGen body₁ σ₁ h_wf_σ₁).1 e he_mem
      obtain ⟨str', h_eq', h_Q'⟩ :=
        LoopInitHoistLoopArmWF.Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix
          hQmint body₁ σ₁ hb
      have h_b_eq' : b = HasIdent.ident str := he_eq.symm.trans h_b_eq
      have h_id : (HasIdent.ident str' : P.Ident) = HasIdent.ident str := h_eq'.symm.trans h_b_eq'
      have : str' = str := LawfulHasIdent.ident_inj h_id
      exact ⟨str, h_b_eq', this ▸ h_Q', this ▸ h_notσ₁⟩
    -- Targets are undef at the source post-store (loop entry undef + no-exit).
    -- Sources/targets disjoint from ambient A/B and from initVars body.
    have h_As_notA : ∀ x ∈ LoopInitHoistLoopDriver.sourcesOf' E, x ∉ A := by
      intro x hx
      rcases h_src_class x hx with h_o | ⟨str, he, hsuf, _, _⟩
      · exact h_lhs_disjoint_body x h_o
      · exact he ▸ (h_src_shapefree_body str hsuf).1
    have h_As_notB : ∀ x ∈ LoopInitHoistLoopDriver.sourcesOf' E, x ∉ B := by
      intro x hx
      rcases h_src_class x hx with h_o | ⟨str, he, hsuf, _, _⟩
      · exact h_extra_disjoint_body x h_o
      · exact he ▸ (h_src_shapefree_body str hsuf).2.1
    have h_B_notAs : ∀ b ∈ B, b ∉ LoopInitHoistLoopDriver.sourcesOf' E :=
      fun b hb hmem => h_As_notB b hmem hb
    have h_Bs_notB : ∀ b ∈ LoopInitHoistLoopDriver.targetsOf' E, b ∉ B := by
      intro b hb
      obtain ⟨str, he, hsuf, _⟩ := h_tgt_class b hb
      exact he ▸ (h_src_shapefree_body str hsuf).2.1
    have h_B_notBs : ∀ b ∈ B, b ∉ LoopInitHoistLoopDriver.targetsOf' E :=
      fun b hb hmem => h_Bs_notB b hmem hb
    have h_ss_wf : ∀ a b, (a, b) ∈ LoopInitHoistLoopDriver.substOf' E →
        a ∈ LoopInitHoistLoopDriver.sourcesOf' E ∧ b ∈ LoopInitHoistLoopDriver.targetsOf' E := by
      intro a b hab
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hab
      cases heq
      exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩, List.mem_map.mpr ⟨e, he, rfl⟩⟩
    -- guard `g'` is shape-free: it never reads a `_<digit>`-suffixed ident.
    have h_guard_sf : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars (ExprOrNondet.det g') := by
      have h := h_exprs_shapefree
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree] at h
      exact h.1.1
    have h_guard_sf' : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ HasVarsPure.getVars g' := by
      intro str h_suf
      have := h_guard_sf str h_suf
      rw [ExprOrNondet.getVars] at this; exact this
    -- the loop's body inits are fresh in its own guard `g'`.
    have h_initVars_notin_guard : ∀ y ∈ Block.initVars body, y ∉ HasVarsPure.getVars g' := by
      have h := h_fresh
      unfold Block.hoistedNamesFreshInRhsAndGuards at h
      rw [Bool.and_eq_true] at h
      have hg := h.1
      simp only [Block.hoistedNamesFreshInGuards, Stmt.hoistedNamesFreshInGuards,
        Bool.and_true, Bool.and_eq_true] at hg
      have hg1 := hg.1
      rw [List.all_eq_true] at hg1
      intro y hy hmem
      have := hg1 y hy
      rw [List.all_eq_true] at this
      have h_in : y ∈ ExprOrNondet.getVars (ExprOrNondet.det g') ++ [] ++ [] := by
        rw [ExprOrNondet.getVars]; simp; exact hmem
      have := this y h_in
      have h_eq : (P.EqIdent y y).decide = true := by simp
      rw [h_eq] at this; exact absurd this (by decide)
    -- guard `g'` freshness from sources/targets.
    have h_g_As_fresh : ∀ x ∈ LoopInitHoistLoopDriver.sourcesOf' E, x ∉ HasVarsPure.getVars g' := by
      intro x hx
      rcases h_src_class x hx with h_o | ⟨str, heq, hsuf, _, _⟩
      · exact h_initVars_notin_guard x h_o
      · exact heq ▸ h_guard_sf' str hsuf
    have h_g_Bs_fresh : ∀ x ∈ LoopInitHoistLoopDriver.targetsOf' E, x ∉ HasVarsPure.getVars g' := by
      intro x hx
      obtain ⟨str, heq, hsuf, _⟩ := h_tgt_class x hx
      exact heq ▸ h_guard_sf' str hsuf
    -- `Vs := initVars body` disjoint from targets (program names vs suffix-shaped).
    have h_Vs_notBs : ∀ y ∈ Block.initVars body, y ∉ LoopInitHoistLoopDriver.targetsOf' E := by
      intro y hy hmem
      obtain ⟨str, he, hsuf, _⟩ := h_tgt_class y hmem
      exact (h_src_shapefree_body str hsuf).2.2.1 (he ▸ hy)
    -- noFuncDecl facts.
    have h_nofd_src : Block.noFuncDecl body = true := Block.noFuncDecl_of_not_containsFuncDecl body h_fd_body
    have h_nofd_h : Block.noFuncDecl body₃ = true := by
      show Block.noFuncDecl
        (Block.applyRenames (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.1
          (Block.liftInitsInLoopBodyM body₁ σ₁).1.2.2) = true
      rw [h_renames_eq]
      exact LoopInitHoistLoopArmWF.Block.stepB_noFuncDecl_h_of_lift hQmint body σ h_wf_σ
        h_nd_body h_fd_body h_inv_body h_measure_body h_unique_body
        h_exprs_shapefree_body h_src_shapefree_body_iv h_mod_disjoint_B1
    -- entry-undef of sources/targets at ρ_hoist (the harvest carriers are undef there).
    have h_src_undef_h : ∀ e ∈ E, ρ_hoist.store e.1 = none := by
      intro e he
      have h_mem : e.1 ∈ LoopInitHoistLoopDriver.sourcesOf' E := List.mem_map.mpr ⟨e, he, rfl⟩
      rcases h_src_class e.1 h_mem with h_o | ⟨str, heq, hsuf, _, hnotσ⟩
      · exact h_hoist_undef_h_body e.1 h_o
      · exact heq ▸ h_hoist_store_shapefree str hsuf hnotσ
    have h_tgt_undef_h : ∀ e ∈ E, ρ_hoist.store e.2.1 = none := by
      intro e he
      have h_mem : e.2.1 ∈ LoopInitHoistLoopDriver.targetsOf' E := List.mem_map.mpr ⟨e, he, rfl⟩
      obtain ⟨str, heq, hsuf, hnotσ₁⟩ := h_tgt_class e.2.1 h_mem
      exact heq ▸ h_hoist_store_shapefree str hsuf
        (fun h => hnotσ₁ ((Block.hoistLoopPrefixInitsM_genStep body σ).subset h))
    -- source-store undef on the harvested sources (ORIGINAL ⇒ initVars body undef;
    -- FRESH ⇒ suffix-shaped ∉ σ undef by the threaded store-shapefree).
    have h_src_As_undef : ∀ a ∈ LoopInitHoistLoopDriver.sourcesOf' E, ρ_src.store a = none := by
      intro a ha
      rcases h_src_class a ha with h_o | ⟨str, he, hsuf, _, hnotσ⟩
      · exact h_hoist_undef_body a h_o
      · exact he ▸ h_src_store_shapefree str hsuf hnotσ
    -- post-store undef of sources/targets via `loopDet_preserves_none_terminal`.
    -- No-exit-free: a `.terminal` source loop run keeps any loop-entry-undefined
    -- carrier undefined (each iteration's `.none`-block projects undefined entries
    -- back to `none`; an inner `.exiting` would propagate the loop to `.exiting`,
    -- not `.terminal`).  The source body need NOT be statically exit-free.
    have h_post_src_none : ∀ (ρ_post : Env P) (x : P.Ident),
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g') none [] body md) ρ_src) (.terminal ρ_post) →
        x ∈ LoopInitHoistLoopDriver.sourcesOf' E → ρ_post.store x = none := by
      intro ρ_post x h_run hx
      exact LoopInitHoistLoopDriver.loopDet_preserves_none_terminal (h_src_As_undef x hx) h_run
    have h_post_tgt_none : ∀ (ρ_post : Env P) (x : P.Ident),
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g') none [] body md) ρ_src) (.terminal ρ_post) →
        x ∈ LoopInitHoistLoopDriver.targetsOf' E → ρ_post.store x = none := by
      intro ρ_post x h_run hx
      refine LoopInitHoistLoopDriver.loopDet_preserves_none_terminal ?_ h_run
      obtain ⟨str, he, hsuf, hnotσ₁⟩ := h_tgt_class x hx
      exact he ▸ h_src_store_shapefree str hsuf
        (fun h => hnotσ₁ ((Block.hoistLoopPrefixInitsM_genStep body σ).subset h))
    -- post-store undef of sources/targets on an EXITING source loop run.  A body
    -- `.exit` is ADMITTED: when some iteration breaks with a label, the loop reaches
    -- `.exiting`.  `loopDet_preserves_none_exiting` (no-exit-free) keeps any
    -- loop-entry-undefined carrier undefined at the exit store — the same
    -- per-iteration `projectStore` invariant, capped by the breaking iteration's
    -- `.none`-block mismatch.  These obligations feed the sum-typed driver's exit
    -- branch, which now genuinely fires on a body `.exit`.
    have h_post_src_none_exit : ∀ (lbl : String) (ρ_post : Env P) (x : P.Ident),
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g') none [] body md) ρ_src) (.exiting lbl ρ_post) →
        x ∈ LoopInitHoistLoopDriver.sourcesOf' E → ρ_post.store x = none := by
      intro lbl ρ_post x h_run hx
      exact LoopInitHoistLoopDriver.loopDet_preserves_none_exiting (h_src_As_undef x hx) h_run
    have h_post_tgt_none_exit : ∀ (lbl : String) (ρ_post : Env P) (x : P.Ident),
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g') none [] body md) ρ_src) (.exiting lbl ρ_post) →
        x ∈ LoopInitHoistLoopDriver.targetsOf' E → ρ_post.store x = none := by
      intro lbl ρ_post x h_run hx
      refine LoopInitHoistLoopDriver.loopDet_preserves_none_exiting ?_ h_run
      obtain ⟨str, he, hsuf, hnotσ₁⟩ := h_tgt_class x hx
      exact he ▸ h_src_store_shapefree str hsuf
        (fun h => hnotσ₁ ((Block.hoistLoopPrefixInitsM_genStep body σ).subset h))
    have h_tgt_nodup : (LoopInitHoistLoopDriver.targetsOf' E).Nodup :=
      (LoopInitHoistLoopArmWF.Block.entriesOf_targetGen body₁ σ₁ h_wf_σ₁).2
    -- σ_sf-relative source-store shape-freedom at ρ_src for the driver.
    have h_arm_src_sf : ∀ str : String, Q str →
        str ∉ StringGenState.stringGens σ → ρ_src.store (HasIdent.ident (P := P) str) = none :=
      h_src_store_shapefree
    have h_sf_notA : ∀ str : String, Q str →
        str ∉ StringGenState.stringGens σ → HasIdent.ident (P := P) str ∉ A :=
      fun str h_suf _ => (h_src_shapefree_body str h_suf).1
    have h_sf_notB : ∀ str : String, Q str →
        str ∉ StringGenState.stringGens σ → HasIdent.ident (P := P) str ∉ B :=
      fun str h_suf _ => (h_src_shapefree_body str h_suf).2.1
    exact LoopInitHoistLoopArmWF.loop_arm_close (σ_sf := σ) (Vs := Block.initVars body)
      (entries := E) (body := body) (body₁ := body₁) (body₃ := body₃) (g := g') (md := md)
      stepA stepA_exit stepB
      h_hoist_undef_body h_hoist_undef_h_body h_arm_src_sf h_sf_notA h_sf_notB
      h_lhs_disjoint_body h_extra_disjoint_body h_Vs_notBs
      h_subst_wf h_ss_wf h_As_notA h_As_notB h_B_notAs h_B_notBs h_Bs_notB
      h_g_A_fresh h_g_B_fresh h_g_As_fresh h_g_Bs_fresh
      h_src_As_undef h_nofd_src h_nofd_h h_tgt_nodup
      h_src_undef_h h_tgt_undef_h h_post_src_none h_post_tgt_none
      h_post_src_none_exit h_post_tgt_none_exit
      h_wfvar h_wfcongr h_wfdef h_hinv h_eval_eq h_hf_eq h_hoist_bound h_run_src h_cfg_src
  | .exit lbl md =>
    subst h_match
    -- Identity residual `[.exit lbl md]`.  Source `.stmt (.exit lbl md) ρ_src` steps
    -- to `.exiting lbl ρ_src`; the hoisted identity does the same.
    have h_residual : (Stmt.hoistLoopPrefixInitsM (.exit lbl md) σ).1 = [.exit lbl md] := by
      rw [Stmt.hoistLoopPrefixInitsM]
    rw [h_residual]
    have h_cfg_eq : cfg_src = .exiting lbl ρ_src := by
      cases h_run_src with
      | refl => rcases h_cfg_src with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact nomatch h
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    refine ⟨ρ_hoist, .exiting lbl ρ_hoist, ?_,
      Or.inr ⟨lbl, ρ_src, h_cfg_eq, rfl, h_hinv, h_hf_eq, h_hoist_bound⟩⟩
    refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
    refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_exit) ?_
    exact ReflTrans.step _ _ _ StepStmt.step_seq_exit (ReflTrans.refl _)
  | .funcDecl d md =>
    subst h_match
    -- Excluded by `h_no_fd`: `Stmt.containsFuncDecl (.funcDecl d md) = true`.
    rw [Stmt.containsFuncDecl] at h_no_fd
    exact absurd h_no_fd (by simp)
  | .typeDecl t md =>
    subst h_match
    -- Identity residual `[.typeDecl t md]`.  A type decl steps to `.terminal ρ_src`.
    have h_residual : (Stmt.hoistLoopPrefixInitsM (.typeDecl t md) σ).1 = [.typeDecl t md] := by
      rw [Stmt.hoistLoopPrefixInitsM]
    rw [h_residual]
    have h_cfg_eq : cfg_src = .terminal ρ_src := by
      cases h_run_src with
      | refl => rcases h_cfg_src with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact nomatch h
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    refine ⟨ρ_hoist, .terminal ρ_hoist, ?_,
      Or.inl ⟨ρ_src, h_cfg_eq, rfl, h_hinv, h_hf_eq, h_hoist_bound⟩⟩
    refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
    refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner StepStmt.step_typeDecl) ?_
    refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  termination_by sizeOf s
  decreasing_by all_goals (subst h_match; simp_wf; omega)

/-- §E Block-level forward simulation IH (= S1 entry point, sum-typed), stated
over the MONADIC pass `Block.hoistLoopPrefixInitsM` at an ARBITRARY input
generator state `σ`.

For a list of statements `ss`, every source run `.stmts ss ρ_src ⟶* cfg_src`
whose final config is either `.terminal ρ_src'` or `.exiting lbl ρ_src'`
admits a matching hoisted run `.stmts (Block.hoistLoopPrefixInitsM ss σ).1
ρ_hoist ⟶* cfg_hoist` to a config of the same shape (terminal/exiting with
the same label) carrying `HoistInv A B subst` and `hasFailure` agreement.

Quantifying over `σ` is what makes the `cons` arm recurse: the residual
`(Block.hoistLoopPrefixInitsM (s :: rest) σ).1` decomposes as
`(head-at-σ) ++ (tail-at-σ')` with `σ' = (Stmt.hoistLoopPrefixInitsM s σ).2`,
and the tail IH instantiates at `σ'` (not at `emp`).  The pure wrapper
`Block.hoistLoopPrefixInits ss` is the `σ = emp` specialization, so the
top-level theorem instantiates this lemma at `σ := StringGenState.emp`.

`h_wf_σ` carries the generator-state well-formedness; `h_src_namesFreshFromσ`
records that every generated label already present in `σ` (mapped through
`HasIdent.ident`) is disjoint from the source program's frame names `A`, extra
names `B`, and `.init` LHS names.  At `σ = emp` the generated-labels list is
empty, so this precondition is vacuously true.

`h_names_fresh_B` is the `B`-side analogue of `h_names_fresh`: the extra names
`B` are fresh in every guard and RHS expression of the block.  `h_src_shapefree`
records that any source identifier carrying the generator's `_<digits>` suffix
shape is disjoint from `A`, `B`, and the `.init` LHS names (front-end source
names never collide with the generator's naming scheme).  `h_subst_wf` records
that every substitution pair `(a, b)` relates an `A`-name to a `B`-name. -/
private theorem Block.hoistLoopPrefixInits_preserves {Q : String → Prop}
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {extendEval : ExtendEval P}
    (A : List P.Ident)
    (B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (ss : List (Stmt P (Cmd P)))
    (σ : StringGenState)
    {ρ_src ρ_hoist : Env P}
    {cfg_src : Config P (Cmd P)}
    (h_no_nd      : Block.containsNondetLoop ss = false)
    (h_no_fd      : Block.containsFuncDecl ss = false)
    (h_no_inv     : Block.loopHasNoInvariants ss = true)
    (h_no_measure : Block.loopMeasureNone ss = true)
    (h_exprs_shapefree : Block.exprsShapeFree (P := P) Q ss)
    (h_unique     : Block.uniqueInits ss)
    (h_fresh      : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss = true)
    (h_names_fresh : Block.namesFreshInExprs A ss = true)
    (h_names_fresh_B : Block.namesFreshInExprs B ss = true)
    (h_lhs_disjoint : ∀ y ∈ Block.initVars ss, y ∉ A)
    (h_extra_disjoint : ∀ y ∈ Block.initVars ss, y ∉ B)
    (h_mod_disjoint_A : ∀ x ∈ Block.modifiedVars ss, x ∉ A)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars ss, x ∉ B)
    (h_hoist_undef : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_hoist_undef_h : ∀ y ∈ Block.initVars ss, ρ_hoist.store y = none)
    (h_src_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_hoist_store_shapefree : ∀ str : String, Q str →
      str ∉ StringGenState.stringGens σ → ρ_hoist.store (HasIdent.ident (P := P) str) = none)
    (h_wf_σ       : StringGenState.WF σ)
    (h_src_namesFreshFromσ :
      ∀ str ∈ StringGenState.stringGens σ,
        HasIdent.ident (P := P) str ∉ A ∧
        HasIdent.ident (P := P) str ∉ B ∧
        HasIdent.ident (P := P) str ∉ Block.initVars ss)
    (h_src_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ A ∧
        HasIdent.ident (P := P) str ∉ B ∧
        HasIdent.ident (P := P) str ∉ Block.initVars ss ∧
        HasIdent.ident (P := P) str ∉ Block.modifiedVars ss)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval_eq    : ρ_src.eval = ρ_hoist.eval)
    (h_hf_eq      : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_hoist_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendEval
                     (.stmts ss ρ_src) cfg_src)
    (h_cfg_src    : (∃ ρ_src' : Env P, cfg_src = .terminal ρ_src') ∨
                    (∃ lbl ρ_src', cfg_src = .exiting lbl ρ_src'))
    (h_wfvar      : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr    : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst    : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef      : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.hoistLoopPrefixInitsM ss σ).1 ρ_hoist) cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            cfg_src = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            cfg_src = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  classical
  match h_match : ss with
  | [] =>
    subst h_match
    -- Empty block: `(...M [] σ).1 = []`.  Source run `.stmts [] ρ_src ⟶* cfg_src`
    -- can only reach `.terminal ρ_src`.  Output `.stmts [] ρ_hoist ⟶ .terminal ρ_hoist`.
    have h_cfg_eq : cfg_src = .terminal ρ_src := by
      cases h_run_src with
      | refl =>
        rcases h_cfg_src with ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact nomatch h
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    refine ⟨ρ_hoist, .terminal ρ_hoist, ?_, Or.inl ⟨ρ_src, h_cfg_eq, rfl, h_hinv, h_hf_eq, h_hoist_bound⟩⟩
    show StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.hoistLoopPrefixInitsM ([] : List (Stmt P (Cmd P))) σ).1 ρ_hoist) (.terminal ρ_hoist)
    simp only [Block.hoistLoopPrefixInitsM]
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | s :: rest =>
    subst h_match
    -- === Decompose the MONADIC residual: head-at-σ ++ tail-at-σ1. ===
    have h_cons_out :
        (Block.hoistLoopPrefixInitsM (s :: rest) σ).1 =
          (Stmt.hoistLoopPrefixInitsM s σ).1 ++
            (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).1 :=
      Block.hoistLoopPrefixInitsM_cons_out s rest σ
    -- === Boolean precondition decomposition: [s] / rest from s::rest. ===
    have h_split_list : (s :: rest : List (Stmt P (Cmd P))) = [s] ++ rest := rfl
    have h_nd_s : Block.containsNondetLoop [s] = false ∧ Block.containsNondetLoop rest = false := by
      rw [h_split_list, Block.containsNondetLoop_append, Bool.or_eq_false_iff] at h_no_nd
      exact h_no_nd
    have h_fd_s : Block.containsFuncDecl [s] = false ∧ Block.containsFuncDecl rest = false := by
      rw [h_split_list, Block.containsFuncDecl_append, Bool.or_eq_false_iff] at h_no_fd
      exact h_no_fd
    have h_inv_s : Block.loopHasNoInvariants [s] = true ∧ Block.loopHasNoInvariants rest = true := by
      rw [h_split_list, Block.loopHasNoInvariants_append, Bool.and_eq_true] at h_no_inv
      exact h_no_inv
    have h_measure_s : Block.loopMeasureNone [s] = true ∧ Block.loopMeasureNone rest = true := by
      rw [h_split_list, Block.loopMeasureNone_append, Bool.and_eq_true] at h_no_measure
      exact h_no_measure
    have h_exprs_shapefree_s :
        Block.exprsShapeFree (P := P) Q [s] ∧
          Block.exprsShapeFree (P := P) Q rest := by
      -- `Block.exprsShapeFree (s :: rest) = Stmt.exprsShapeFree s ∧ Block.exprsShapeFree rest`
      -- and `Block.exprsShapeFree [s] = Stmt.exprsShapeFree s ∧ True`.
      have h := h_exprs_shapefree
      simp only [Block.exprsShapeFree] at h ⊢
      exact ⟨⟨h.1, True.intro⟩, h.2⟩
    have h_iv_split : Block.initVars (s :: rest) = Block.initVars [s] ++ Block.initVars rest := by
      rw [h_split_list, Block.initVars_append]
    have h_mod_split : Block.modifiedVars (s :: rest) =
        Block.modifiedVars [s] ++ Block.modifiedVars rest := by
      simp only [Block.modifiedVars, List.append_nil]
    have h_unique_full : (Block.initVars [s] ++ Block.initVars rest).Nodup := by
      have : Block.uniqueInits (s :: rest) = (Block.initVars (s :: rest)).Nodup := rfl
      rw [this, h_iv_split] at h_unique; exact h_unique
    have h_unique_s : Block.uniqueInits [s] := by
      show (Block.initVars [s]).Nodup
      exact (List.nodup_append.mp h_unique_full).1
    have h_unique_rest : Block.uniqueInits rest := by
      show (Block.initVars rest).Nodup
      exact (List.nodup_append.mp h_unique_full).2.1
    have h_fresh_unfold := h_fresh
    unfold Block.hoistedNamesFreshInRhsAndGuards at h_fresh_unfold
    rw [Bool.and_eq_true] at h_fresh_unfold
    obtain ⟨h_guards_full, h_namesFresh_full⟩ := h_fresh_unfold
    rw [show Block.hoistedNamesFreshInGuards (s :: rest) =
          (Stmt.hoistedNamesFreshInGuards s && Block.hoistedNamesFreshInGuards rest) from by
          rw [Block.hoistedNamesFreshInGuards], Bool.and_eq_true] at h_guards_full
    obtain ⟨h_guards_s_stmt, h_guards_rest⟩ := h_guards_full
    have h_guards_s : Block.hoistedNamesFreshInGuards [s] = true := by
      simp only [Block.hoistedNamesFreshInGuards, Bool.and_true]; exact h_guards_s_stmt
    have h_nf_cons :
        Block.namesFreshInRhsExprs (Block.initVars (s :: rest)) (s :: rest) =
          (Stmt.namesFreshInRhsExprs (Block.initVars (s :: rest)) s &&
            Block.namesFreshInRhsExprs (Block.initVars (s :: rest)) rest) := by
      rw [Block.namesFreshInRhsExprs]
    rw [h_nf_cons, Bool.and_eq_true] at h_namesFresh_full
    obtain ⟨h_nf_s_full, h_nf_rest_full⟩ := h_namesFresh_full
    have h_sub_s : (Block.initVars [s] : List P.Ident) ⊆ Block.initVars (s :: rest) := by
      rw [h_iv_split]; exact fun _ h => List.mem_append.mpr (Or.inl h)
    have h_sub_rest : (Block.initVars rest : List P.Ident) ⊆ Block.initVars (s :: rest) := by
      rw [h_iv_split]; exact fun _ h => List.mem_append.mpr (Or.inr h)
    have h_nf_s_block : Block.namesFreshInRhsExprs (Block.initVars (s :: rest)) [s] = true := by
      simp only [Block.namesFreshInRhsExprs, Bool.and_true]; exact h_nf_s_full
    have h_fresh_s : Block.hoistedNamesFreshInRhsAndGuards (P := P) [s] = true := by
      unfold Block.hoistedNamesFreshInRhsAndGuards
      rw [Bool.and_eq_true]
      exact ⟨h_guards_s, Block.namesFreshInRhsExprs_subset h_sub_s [s] h_nf_s_block⟩
    have h_fresh_rest : Block.hoistedNamesFreshInRhsAndGuards (P := P) rest = true := by
      unfold Block.hoistedNamesFreshInRhsAndGuards
      rw [Bool.and_eq_true]
      exact ⟨h_guards_rest, Block.namesFreshInRhsExprs_subset h_sub_rest rest h_nf_rest_full⟩
    have h_names_fresh_cons :
        Block.namesFreshInExprs A (s :: rest) =
          (Stmt.namesFreshInExprs A s && Block.namesFreshInExprs A rest) := by
      rw [Block.namesFreshInExprs]
    rw [h_names_fresh_cons, Bool.and_eq_true] at h_names_fresh
    obtain ⟨h_names_fresh_s_stmt, h_names_fresh_rest⟩ := h_names_fresh
    have h_names_fresh_s : Block.namesFreshInExprs A [s] = true := by
      simp only [Block.namesFreshInExprs, Bool.and_true]; exact h_names_fresh_s_stmt
    have h_names_fresh_B_cons :
        Block.namesFreshInExprs B (s :: rest) =
          (Stmt.namesFreshInExprs B s && Block.namesFreshInExprs B rest) := by
      rw [Block.namesFreshInExprs]
    rw [h_names_fresh_B_cons, Bool.and_eq_true] at h_names_fresh_B
    obtain ⟨h_names_fresh_B_s_stmt, h_names_fresh_B_rest⟩ := h_names_fresh_B
    have h_names_fresh_B_s : Block.namesFreshInExprs B [s] = true := by
      simp only [Block.namesFreshInExprs, Bool.and_true]; exact h_names_fresh_B_s_stmt
    have h_lhs_disjoint_s : ∀ y ∈ Block.initVars [s], y ∉ A := fun y hy =>
      h_lhs_disjoint y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl hy))
    have h_lhs_disjoint_rest : ∀ y ∈ Block.initVars rest, y ∉ A := fun y hy =>
      h_lhs_disjoint y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
    have h_extra_disjoint_s : ∀ y ∈ Block.initVars [s], y ∉ B := fun y hy =>
      h_extra_disjoint y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl hy))
    have h_extra_disjoint_rest : ∀ y ∈ Block.initVars rest, y ∉ B := fun y hy =>
      h_extra_disjoint y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
    have h_mod_disjoint_A_s : ∀ x ∈ Block.modifiedVars [s], x ∉ A := fun x hx =>
      h_mod_disjoint_A x (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inl hx))
    have h_mod_disjoint_A_rest : ∀ x ∈ Block.modifiedVars rest, x ∉ A := fun x hx =>
      h_mod_disjoint_A x (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inr hx))
    have h_mod_disjoint_B_s : ∀ x ∈ Block.modifiedVars [s], x ∉ B := fun x hx =>
      h_mod_disjoint_B x (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inl hx))
    have h_mod_disjoint_B_rest : ∀ x ∈ Block.modifiedVars rest, x ∉ B := fun x hx =>
      h_mod_disjoint_B x (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inr hx))
    have h_hoist_undef_s : ∀ y ∈ Block.initVars [s], ρ_src.store y = none := fun y hy =>
      h_hoist_undef y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl hy))
    have h_hoist_undef_h_s : ∀ y ∈ Block.initVars [s], ρ_hoist.store y = none := fun y hy =>
      h_hoist_undef_h y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl hy))
    have h_src_fresh_s :
        ∀ str ∈ StringGenState.stringGens σ,
          HasIdent.ident (P := P) str ∉ A ∧
          HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars [s] := by
      intro str hstr
      obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
      exact ⟨hA, hB, fun h => hiv (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl h))⟩
    have h_src_shapefree_s :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧
          HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars [s] ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars [s] := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl h)),
        fun h => hmv (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inl h))⟩
    have h_src_shapefree_rest :
        ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ A ∧
          HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars rest ∧
          HasIdent.ident (P := P) str ∉ Block.modifiedVars rest := by
      intro str hstr
      obtain ⟨hA, hB, hiv, hmv⟩ := h_src_shapefree str hstr
      exact ⟨hA, hB, fun h => hiv (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr h)),
        fun h => hmv (by rw [h_mod_split]; exact List.mem_append.mpr (Or.inr h))⟩
    have h_genStep_head : StringGenState.GenStep σ (Stmt.hoistLoopPrefixInitsM s σ).2 :=
      Stmt.hoistLoopPrefixInitsM_genStep s σ
    have h_wf_σ1 : StringGenState.WF (Stmt.hoistLoopPrefixInitsM s σ).2 :=
      h_genStep_head.wf_mono h_wf_σ
    have h_src_fresh_σ1 :
        SrcNamesFreshFromGen (P := P) A B (Block.initVars rest)
          (Stmt.hoistLoopPrefixInitsM s σ).2 := by
      have h_fresh_σ_rest : SrcNamesFreshFromGen (P := P) A B (Block.initVars rest) σ := by
        intro str hstr
        obtain ⟨hA, hB, hiv⟩ := h_src_namesFreshFromσ str hstr
        exact ⟨hA, hB, fun h => hiv (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr h))⟩
      exact SrcNamesFreshFromGen.genStep_of_delta
        (Stmt.hoistLoopPrefixInitsM_genStep_delta_Q hQmint s σ)
        (fun str hsuf => let ⟨a, b, c, _⟩ := h_src_shapefree_rest str hsuf; ⟨a, b, c⟩) h_fresh_σ_rest
    have h_src_fresh_rest :
        ∀ str ∈ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2,
          HasIdent.ident (P := P) str ∉ A ∧
          HasIdent.ident (P := P) str ∉ B ∧
          HasIdent.ident (P := P) str ∉ Block.initVars rest := h_src_fresh_σ1
    -- === Split the SOURCE run into head + tail, dispatch on cfg_src. ===
    rw [h_cons_out]
    rcases h_cfg_src with ⟨ρ_src', h_term⟩ | ⟨lbl, ρ_src', h_exit⟩
    · -- TERMINAL: cfg_src = .terminal ρ_src'.
      subst h_term
      have h_run_src' : StepStmtStar P (EvalCmd P) extendEval
          (.stmts ([s] ++ rest) ρ_src) (.terminal ρ_src') := h_run_src
      obtain ⟨ρ_s_mid, h_head_src, h_tail_src⟩ :=
        stmts_append_terminates P (EvalCmd P) extendEval [s] rest ρ_src ρ_src' h_run_src'
      have h_head_stmt : StepStmtStar P (EvalCmd P) extendEval
          (.stmt s ρ_src) (.terminal ρ_s_mid) := by
        cases h_head_src with
        | step _ _ _ h1 hr1 =>
          cases h1
          obtain ⟨ρ_m, h_s_term, h_nil⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hr1
          cases h_nil with
          | step _ _ _ h2 hr2 =>
            cases h2
            cases hr2 with
            | refl => exact h_s_term
            | step _ _ _ hd _ => exact nomatch hd
      have h_nd_stmt : Stmt.containsNondetLoop s = false := by
        rw [Block.containsNondetLoop, Bool.or_eq_false_iff] at h_nd_s; exact h_nd_s.1.1
      have h_fd_stmt : Stmt.containsFuncDecl s = false := by
        rw [Block.containsFuncDecl, Bool.or_eq_false_iff] at h_fd_s; exact h_fd_s.1.1
      have h_inv_stmt : Stmt.loopHasNoInvariants s = true := by
        rw [Block.loopHasNoInvariants, Bool.and_eq_true] at h_inv_s; exact h_inv_s.1.1
      have h_measure_stmt : Stmt.loopMeasureNone s = true := by
        rw [Block.loopMeasureNone, Bool.and_eq_true] at h_measure_s; exact h_measure_s.1.1
      -- HEAD §E Stmt-IH at σ.
      obtain ⟨ρ_h_mid, cfg_h_head, h_head_hoist, h_head_outcome⟩ :=
        Stmt.hoistLoopPrefixInits_preserves hQmint A B subst s σ
          h_nd_stmt h_fd_stmt h_inv_stmt h_measure_stmt h_exprs_shapefree_s.1 h_unique_s h_fresh_s
          h_names_fresh_s h_names_fresh_B_s h_lhs_disjoint_s h_extra_disjoint_s
          h_mod_disjoint_A_s h_mod_disjoint_B_s h_hoist_undef_s h_hoist_undef_h_s
          h_src_store_shapefree h_hoist_store_shapefree
          h_wf_σ h_src_fresh_s h_src_shapefree_s h_subst_wf h_hinv h_eval_eq h_hf_eq h_hoist_bound
          h_head_stmt (Or.inl ⟨ρ_s_mid, rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
      obtain ⟨h_cfg_h_eq, h_hinv_mid, h_hf_mid, h_bound_mid⟩ :
            cfg_h_head = .terminal ρ_h_mid ∧
            HoistInv (P := P) A B subst ρ_s_mid.store ρ_h_mid.store ∧
            ρ_s_mid.hasFailure = ρ_h_mid.hasFailure ∧ (∀ y ∈ B, ρ_h_mid.store y ≠ none) := by
        rcases h_head_outcome with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1, _, _, _, _⟩
        · have hr_eq : r = ρ_s_mid := by
            simp only [Config.terminal.injEq] at hr1; exact hr1.symm
          subst hr_eq; exact ⟨hr2, hr3, hr4, hr5⟩
        · exact absurd hr1 (by simp)
      subst h_cfg_h_eq
      have h_src_s_nofd : Stmt.noFuncDecl s = true :=
        Stmt.noFuncDecl_of_not_containsFuncDecl s h_fd_stmt
      have h_residual_nofd :
          Block.noFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 = true := by
        apply Block.noFuncDecl_of_not_containsFuncDecl
        rw [Stmt.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_fd_stmt
      have h_src_mid_eval : ρ_s_mid.eval = ρ_src.eval :=
        smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval s ρ_src ρ_s_mid
          h_src_s_nofd h_head_stmt
      have h_h_mid_eval : ρ_h_mid.eval = ρ_hoist.eval :=
        smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          (Stmt.hoistLoopPrefixInitsM s σ).1 ρ_hoist ρ_h_mid h_residual_nofd h_head_hoist
      have h_eval_mid : ρ_s_mid.eval = ρ_h_mid.eval := by
        rw [h_src_mid_eval, h_h_mid_eval, h_eval_eq]
      -- TAIL §E Block-IH at σ1.
      obtain ⟨ρ_h_fin, cfg_hoist_tail, h_tail_hoist, h_tail_outcome⟩ :=
        Block.hoistLoopPrefixInits_preserves hQmint A B subst rest (Stmt.hoistLoopPrefixInitsM s σ).2
          h_nd_s.2 h_fd_s.2 h_inv_s.2 h_measure_s.2 h_exprs_shapefree_s.2 h_unique_rest h_fresh_rest
          h_names_fresh_rest h_names_fresh_B_rest h_lhs_disjoint_rest h_extra_disjoint_rest
          h_mod_disjoint_A_rest h_mod_disjoint_B_rest
          (by
            intro y hy
            have h_y_src_none : ρ_src.store y = none :=
              h_hoist_undef y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
            have h_y_not_init_s : y ∉ Block.initVars [s] := fun hc =>
              (List.nodup_append.mp h_unique_full).2.2 y hc y hy rfl
            have h_y_not_def_s : y ∉ Stmt.definedVars (P := P) (C := Cmd P) s := by
              rw [Stmt.definedVars_eq_initVars_of_no_fd s h_fd_stmt]
              intro hc
              exact h_y_not_init_s (by simp only [Block.initVars, List.append_nil]; exact hc)
            exact stmt_run_terminal_preserves_none h_y_src_none h_y_not_def_s h_head_stmt)
          (by
            -- Hoist-side tail undefinedness: the head residual run from `ρ_hoist`
            -- to `ρ_h_mid` cannot touch any `y ∈ Block.initVars rest` because
            -- such `y` is shape-free and disjoint from `s`'s inits, hence is not
            -- among the residual's inits.
            intro y hy
            have h_y_h_none : ρ_hoist.store y = none :=
              h_hoist_undef_h y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
            have h_unique_s_stmt : (Stmt.initVars s).Nodup := by
              have : (Block.initVars [s]).Nodup := h_unique_s
              simpa only [Block.initVars, List.append_nil] using this
            have h_shapefree_s_stmt : ∀ str : String, Q str →
                HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
              intro str h_shape hc
              exact (h_src_shapefree_s str h_shape).2.2.1
                (by simp only [Block.initVars, List.append_nil]; exact hc)
            have h_y_not_src : y ∉ Stmt.initVars s := fun hc =>
              (List.nodup_append.mp h_unique_full).2.2 y
                (by simp only [Block.initVars, List.append_nil]; exact hc) y hy rfl
            have h_y_shapefree : ∀ str : String, y = HasIdent.ident str →
                ¬ Q str := by
              intro str h_y_eq h_shape
              exact (h_src_shapefree str h_shape).2.2.1
                (h_y_eq ▸ (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy)))
            exact residual_run_terminal_preserves_none hQmint h_wf_σ h_unique_s_stmt
              h_shapefree_s_stmt h_fd_stmt h_y_not_src h_y_shapefree h_y_h_none h_head_hoist)
          (by
            -- Mid-store source store-shapefree (at σ1): a suffix-shaped name `z` with
            -- `str ∉ stringGens σ1` is undefined in `ρ_src` (by `h_src_store_shapefree`,
            -- since `str ∉ stringGens σ1 ⊇ stringGens σ`) and is not defined by `s`
            -- (suffix-shaped names lie outside `s`'s inits, hence outside its defined
            -- vars), so the head run from `ρ_src` to `ρ_s_mid` leaves `z` undefined.
            intro str h_shape h_notσ1
            have h_notσ : str ∉ StringGenState.stringGens σ :=
              fun h => h_notσ1 (h_genStep_head.subset h)
            have h_z_src_none : ρ_src.store (HasIdent.ident (P := P) str) = none :=
              h_src_store_shapefree str h_shape h_notσ
            have h_z_not_def_s :
                HasIdent.ident (P := P) str ∉ Stmt.definedVars (P := P) (C := Cmd P) s := by
              rw [Stmt.definedVars_eq_initVars_of_no_fd s h_fd_stmt]
              intro hc
              exact (h_src_shapefree str h_shape).2.2.1
                (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl
                  (by simp only [Block.initVars, List.append_nil]; exact hc)))
            exact stmt_run_terminal_preserves_none h_z_src_none h_z_not_def_s h_head_stmt)
          (by
            -- Mid-store hoist store-shapefree (at σ1): a suffix-shaped name `z = ident str`
            -- with `str ∉ stringGens σ1` is undefined in `ρ_hoist` (by `h_hoist_store_shapefree`,
            -- since `str ∉ stringGens σ1 ⊇ stringGens σ`).  It is not among the head
            -- residual's `initVars`: each is classified as an ORIGINAL init of `s`
            -- (excluded — `z` is suffix-shaped, outside `s`'s inits) or a FRESH name
            -- `str' ∈ stringGens σ1` (excluded — `ident str = ident str'` ⇒ `str = str' ∈
            -- stringGens σ1`, contradicting `str ∉ stringGens σ1`).  So the head residual
            -- run from `ρ_hoist` to `ρ_h_mid` leaves `z` undefined.
            intro str h_shape h_notσ1
            have h_notσ : str ∉ StringGenState.stringGens σ :=
              fun h => h_notσ1 (h_genStep_head.subset h)
            have h_z_h_none : ρ_hoist.store (HasIdent.ident (P := P) str) = none :=
              h_hoist_store_shapefree str h_shape h_notσ
            have h_unique_s_stmt : (Stmt.initVars s).Nodup := by
              have : (Block.initVars [s]).Nodup := h_unique_s
              simpa only [Block.initVars, List.append_nil] using this
            have h_shapefree_s_stmt : ∀ str : String, Q str →
                HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
              intro str' h_shape' hc
              exact (h_src_shapefree_s str' h_shape').2.2.1
                (by simp only [Block.initVars, List.append_nil]; exact hc)
            have h_z_not_residual :
                HasIdent.ident (P := P) str ∉ Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1 := by
              intro h_mem
              have h_class :=
                (LoopInitHoistLoopArmWF.Stmt.hoistLoopPrefixInitsM_initVars_classified
                  hQmint s σ h_wf_σ h_unique_s_stmt h_shapefree_s_stmt).1 _ h_mem
              rcases h_class with h_orig | ⟨str', h_eq, h_str'_in, _, _⟩
              · exact h_shapefree_s_stmt str h_shape h_orig
              · exact h_notσ1 ((LawfulHasIdent.ident_inj h_eq) ▸ h_str'_in)
            have h_residual_contains_nofd :
                Block.containsFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 = false := by
              rw [Stmt.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_fd_stmt
            exact block_run_terminal_preserves_none_of_not_initVars
              h_residual_contains_nofd h_z_not_residual h_z_h_none h_head_hoist)
          h_wf_σ1 h_src_fresh_rest h_src_shapefree_rest h_subst_wf h_hinv_mid h_eval_mid h_hf_mid h_bound_mid
          h_tail_src (Or.inl ⟨ρ_src', rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
      -- === GLUE: chain the head residual run into the tail entry, then the tail. ===
      refine ⟨ρ_h_fin, cfg_hoist_tail, ?_, ?_⟩
      · refine ReflTrans_Transitive _ _ _ _
          (stmts_prefix_terminal_append P (EvalCmd P) extendEval
            (Stmt.hoistLoopPrefixInitsM s σ).1
            (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).1
            ρ_hoist ρ_h_mid h_head_hoist) ?_
        exact h_tail_hoist
      · rcases h_tail_outcome with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1, _, _, _, _⟩
        · exact Or.inl ⟨r, hr1, hr2, hr3, hr4, hr5⟩
        · exact absurd hr1 (by simp)
    · -- EXITING: cfg_src = .exiting lbl ρ_src'.
      subst h_exit
      have h_nd_stmt : Stmt.containsNondetLoop s = false := by
        rw [Block.containsNondetLoop, Bool.or_eq_false_iff] at h_nd_s; exact h_nd_s.1.1
      have h_fd_stmt : Stmt.containsFuncDecl s = false := by
        rw [Block.containsFuncDecl, Bool.or_eq_false_iff] at h_fd_s; exact h_fd_s.1.1
      have h_inv_stmt : Stmt.loopHasNoInvariants s = true := by
        rw [Block.loopHasNoInvariants, Bool.and_eq_true] at h_inv_s; exact h_inv_s.1.1
      have h_measure_stmt : Stmt.loopMeasureNone s = true := by
        rw [Block.loopMeasureNone, Bool.and_eq_true] at h_measure_s; exact h_measure_s.1.1
      have h_residual_nofd :
          Block.noFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 = true := by
        apply Block.noFuncDecl_of_not_containsFuncDecl
        rw [Stmt.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_fd_stmt
      cases h_run_src with
      | step _ _ _ h1 hr1 =>
        cases h1
        rcases seq_reaches_exiting P (EvalCmd P) extendEval hr1 with
          h_head_exit | ⟨ρ_s_mid, h_head_term, h_tail_exit⟩
        · -- HEAD exits: tail never runs.
          obtain ⟨ρ_h_fin, cfg_h_head, h_head_hoist, h_head_outcome⟩ :=
            Stmt.hoistLoopPrefixInits_preserves hQmint A B subst s σ
              h_nd_stmt h_fd_stmt h_inv_stmt h_measure_stmt h_exprs_shapefree_s.1 h_unique_s h_fresh_s
              h_names_fresh_s h_names_fresh_B_s h_lhs_disjoint_s h_extra_disjoint_s
              h_mod_disjoint_A_s h_mod_disjoint_B_s h_hoist_undef_s h_hoist_undef_h_s
              h_src_store_shapefree h_hoist_store_shapefree
              h_wf_σ h_src_fresh_s h_src_shapefree_s h_subst_wf h_hinv h_eval_eq h_hf_eq h_hoist_bound
              h_head_exit (Or.inr ⟨lbl, ρ_src', rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
          obtain ⟨h_cfg_h_eq, h_hinv_fin, h_hf_fin, h_bound_fin⟩ :
                cfg_h_head = .exiting lbl ρ_h_fin ∧
                HoistInv (P := P) A B subst ρ_src'.store ρ_h_fin.store ∧
                ρ_src'.hasFailure = ρ_h_fin.hasFailure ∧ (∀ y ∈ B, ρ_h_fin.store y ≠ none) := by
            rcases h_head_outcome with ⟨r, hr1, _, _, _, _⟩ | ⟨l, r, hr1, hr2, hr3, hr4, hr5⟩
            · exact absurd hr1.symm (by simp)
            · obtain ⟨hl, hr_eq⟩ : l = lbl ∧ r = ρ_src' := by
                simp only [Config.exiting.injEq] at hr1; exact ⟨hr1.1.symm, hr1.2.symm⟩
              subst hl; subst hr_eq; exact ⟨hr2, hr3, hr4, hr5⟩
          subst h_cfg_h_eq
          refine ⟨ρ_h_fin, .exiting lbl ρ_h_fin, ?_, Or.inr ⟨lbl, ρ_src', rfl, rfl, h_hinv_fin, h_hf_fin, h_bound_fin⟩⟩
          exact stmts_prefix_exiting_append P (EvalCmd P) extendEval
            (Stmt.hoistLoopPrefixInitsM s σ).1
            (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).1
            ρ_hoist ρ_h_fin lbl h_head_hoist
        · -- HEAD terminates at ρ_s_mid, TAIL exits.
          have h_head_stmt : StepStmtStar P (EvalCmd P) extendEval
              (.stmt s ρ_src) (.terminal ρ_s_mid) := h_head_term
          obtain ⟨ρ_h_mid, cfg_h_head, h_head_hoist, h_head_outcome⟩ :=
            Stmt.hoistLoopPrefixInits_preserves hQmint A B subst s σ
              h_nd_stmt h_fd_stmt h_inv_stmt h_measure_stmt h_exprs_shapefree_s.1 h_unique_s h_fresh_s
              h_names_fresh_s h_names_fresh_B_s h_lhs_disjoint_s h_extra_disjoint_s
              h_mod_disjoint_A_s h_mod_disjoint_B_s h_hoist_undef_s h_hoist_undef_h_s
              h_src_store_shapefree h_hoist_store_shapefree
              h_wf_σ h_src_fresh_s h_src_shapefree_s h_subst_wf h_hinv h_eval_eq h_hf_eq h_hoist_bound
              h_head_stmt (Or.inl ⟨ρ_s_mid, rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
          obtain ⟨h_cfg_h_eq, h_hinv_mid, h_hf_mid, h_bound_mid⟩ :
                cfg_h_head = .terminal ρ_h_mid ∧
                HoistInv (P := P) A B subst ρ_s_mid.store ρ_h_mid.store ∧
                ρ_s_mid.hasFailure = ρ_h_mid.hasFailure ∧ (∀ y ∈ B, ρ_h_mid.store y ≠ none) := by
            rcases h_head_outcome with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨l, r, hr1, _, _, _, _⟩
            · have hr_eq : r = ρ_s_mid := by
                simp only [Config.terminal.injEq] at hr1; exact hr1.symm
              subst hr_eq; exact ⟨hr2, hr3, hr4, hr5⟩
            · exact absurd hr1 (by simp)
          subst h_cfg_h_eq
          have h_src_s_nofd : Stmt.noFuncDecl s = true :=
            Stmt.noFuncDecl_of_not_containsFuncDecl s h_fd_stmt
          have h_src_mid_eval : ρ_s_mid.eval = ρ_src.eval :=
            smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval s ρ_src ρ_s_mid
              h_src_s_nofd h_head_stmt
          have h_h_mid_eval : ρ_h_mid.eval = ρ_hoist.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              (Stmt.hoistLoopPrefixInitsM s σ).1 ρ_hoist ρ_h_mid h_residual_nofd h_head_hoist
          have h_eval_mid : ρ_s_mid.eval = ρ_h_mid.eval := by
            rw [h_src_mid_eval, h_h_mid_eval, h_eval_eq]
          have h_hoist_undef_mid : ∀ y ∈ Block.initVars rest, ρ_s_mid.store y = none := by
            intro y hy
            have h_y_src_none : ρ_src.store y = none :=
              h_hoist_undef y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
            have h_y_not_init_s : y ∉ Block.initVars [s] := fun hc =>
              (List.nodup_append.mp h_unique_full).2.2 y hc y hy rfl
            have h_y_not_def_s : y ∉ Stmt.definedVars (P := P) (C := Cmd P) s := by
              rw [Stmt.definedVars_eq_initVars_of_no_fd s h_fd_stmt]
              intro hc
              exact h_y_not_init_s (by simp only [Block.initVars, List.append_nil]; exact hc)
            exact stmt_run_terminal_preserves_none h_y_src_none h_y_not_def_s h_head_stmt
          have h_hoist_undef_h_mid : ∀ y ∈ Block.initVars rest, ρ_h_mid.store y = none := by
            intro y hy
            have h_y_h_none : ρ_hoist.store y = none :=
              h_hoist_undef_h y (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy))
            have h_unique_s_stmt : (Stmt.initVars s).Nodup := by
              have : (Block.initVars [s]).Nodup := h_unique_s
              simpa only [Block.initVars, List.append_nil] using this
            have h_shapefree_s_stmt : ∀ str : String, Q str →
                HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
              intro str h_shape hc
              exact (h_src_shapefree_s str h_shape).2.2.1
                (by simp only [Block.initVars, List.append_nil]; exact hc)
            have h_y_not_src : y ∉ Stmt.initVars s := fun hc =>
              (List.nodup_append.mp h_unique_full).2.2 y
                (by simp only [Block.initVars, List.append_nil]; exact hc) y hy rfl
            have h_y_shapefree : ∀ str : String, y = HasIdent.ident str →
                ¬ Q str := by
              intro str h_y_eq h_shape
              exact (h_src_shapefree str h_shape).2.2.1
                (h_y_eq ▸ (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inr hy)))
            exact residual_run_terminal_preserves_none hQmint h_wf_σ h_unique_s_stmt
              h_shapefree_s_stmt h_fd_stmt h_y_not_src h_y_shapefree h_y_h_none h_head_hoist
          -- Mid-store store-shapefree (σ1-relative) for the tail: same derivation as the
          -- terminal branch — the head run defines no `Q`-kind name `str ∉ stringGens σ1`.
          have h_src_store_shapefree_mid : ∀ str : String, Q str →
              str ∉ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2 →
              ρ_s_mid.store (HasIdent.ident (P := P) str) = none := by
            intro str h_shape h_notσ1
            have h_notσ : str ∉ StringGenState.stringGens σ :=
              fun h => h_notσ1 (h_genStep_head.subset h)
            have h_z_src_none : ρ_src.store (HasIdent.ident (P := P) str) = none :=
              h_src_store_shapefree str h_shape h_notσ
            have h_z_not_def_s :
                HasIdent.ident (P := P) str ∉ Stmt.definedVars (P := P) (C := Cmd P) s := by
              rw [Stmt.definedVars_eq_initVars_of_no_fd s h_fd_stmt]
              intro hc
              exact (h_src_shapefree str h_shape).2.2.1
                (by rw [h_iv_split]; exact List.mem_append.mpr (Or.inl
                  (by simp only [Block.initVars, List.append_nil]; exact hc)))
            exact stmt_run_terminal_preserves_none h_z_src_none h_z_not_def_s h_head_stmt
          have h_hoist_store_shapefree_mid : ∀ str : String, Q str →
              str ∉ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2 →
              ρ_h_mid.store (HasIdent.ident (P := P) str) = none := by
            intro str h_shape h_notσ1
            have h_notσ : str ∉ StringGenState.stringGens σ :=
              fun h => h_notσ1 (h_genStep_head.subset h)
            have h_z_h_none : ρ_hoist.store (HasIdent.ident (P := P) str) = none :=
              h_hoist_store_shapefree str h_shape h_notσ
            have h_unique_s_stmt : (Stmt.initVars s).Nodup := by
              have : (Block.initVars [s]).Nodup := h_unique_s
              simpa only [Block.initVars, List.append_nil] using this
            have h_shapefree_s_stmt : ∀ str : String, Q str →
                HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
              intro str' h_shape' hc
              exact (h_src_shapefree_s str' h_shape').2.2.1
                (by simp only [Block.initVars, List.append_nil]; exact hc)
            have h_z_not_residual :
                HasIdent.ident (P := P) str ∉ Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1 := by
              intro h_mem
              have h_class :=
                (LoopInitHoistLoopArmWF.Stmt.hoistLoopPrefixInitsM_initVars_classified
                  hQmint s σ h_wf_σ h_unique_s_stmt h_shapefree_s_stmt).1 _ h_mem
              rcases h_class with h_orig | ⟨str', h_eq, h_str'_in, _, _⟩
              · exact h_shapefree_s_stmt str h_shape h_orig
              · exact h_notσ1 ((LawfulHasIdent.ident_inj h_eq) ▸ h_str'_in)
            have h_residual_contains_nofd :
                Block.containsFuncDecl (Stmt.hoistLoopPrefixInitsM s σ).1 = false := by
              rw [Stmt.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_fd_stmt
            exact block_run_terminal_preserves_none_of_not_initVars
              h_residual_contains_nofd h_z_not_residual h_z_h_none h_head_hoist
          obtain ⟨ρ_h_fin, cfg_hoist_tail, h_tail_hoist, h_tail_outcome⟩ :=
            Block.hoistLoopPrefixInits_preserves hQmint A B subst rest (Stmt.hoistLoopPrefixInitsM s σ).2
              h_nd_s.2 h_fd_s.2 h_inv_s.2 h_measure_s.2 h_exprs_shapefree_s.2 h_unique_rest h_fresh_rest
              h_names_fresh_rest h_names_fresh_B_rest h_lhs_disjoint_rest h_extra_disjoint_rest
              h_mod_disjoint_A_rest h_mod_disjoint_B_rest h_hoist_undef_mid h_hoist_undef_h_mid
              h_src_store_shapefree_mid h_hoist_store_shapefree_mid
              h_wf_σ1 h_src_fresh_rest h_src_shapefree_rest h_subst_wf h_hinv_mid h_eval_mid h_hf_mid h_bound_mid
              h_tail_exit (Or.inr ⟨lbl, ρ_src', rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
          refine ⟨ρ_h_fin, cfg_hoist_tail, ?_, ?_⟩
          · refine ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendEval
                (Stmt.hoistLoopPrefixInitsM s σ).1
                (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).1
                ρ_hoist ρ_h_mid h_head_hoist) ?_
            exact h_tail_hoist
          · rcases h_tail_outcome with ⟨r, hr1, _, _, _, _⟩ | ⟨l, r, hr1, hr2, hr3, hr4, hr5⟩
            · exact absurd hr1.symm (by simp)
            · exact Or.inr ⟨l, r, hr1, hr2, hr3, hr4, hr5⟩
  termination_by sizeOf ss
  decreasing_by all_goals (subst h_match; simp_wf; omega)

end

/-! ### The loop-init-hoist label *kind*

`hoistLoopPrefixInits` mints labels under exactly one prefix, `hoistFreshPrefix`
(`"_hoist"`).  `hoistKind s` is the precise predicate "`s` is a label this pass
could have minted": it carries the `hoistFreshPrefix` generator prefix and is
equal to some `gen` output.  This is the per-kind `Q` to instantiate the
kind-generalized soundness at, replacing the blanket `HasUnderscoreDigitSuffix`
(which would overcommit a composition partner to keeping *every* gen-shaped name
fresh). -/

/-- A label that `hoistLoopPrefixInits` could have minted: it carries the
`hoistFreshPrefix` generator prefix and equals a corresponding `gen` output. -/
@[expose] def hoistKind (s : String) : Prop :=
  ∃ sg, String.HasGenPrefix hoistFreshPrefix s
      ∧ s = (StringGenState.gen hoistFreshPrefix sg).1

/-- The single prefix `hoistLoopPrefixInits` mints under lands inside
`hoistKind`: this is exactly the `hQmint` obligation at `Q := hoistKind`. -/
theorem hoistKind_gen :
    ∀ sg, hoistKind (StringGenState.gen hoistFreshPrefix sg).1 :=
  fun sg => ⟨sg, StringGenState.gen_hasGenPrefix hoistFreshPrefix sg, rfl⟩

/-- Kind-generalized soundness of the loop-init hoist: the pass is sound for any
source program whose `hoistKind`-labelled slots are undefined / unwritten — only
the labels *this* pass mints, not every gen-shaped name.  This weaker entry
precondition is what lets a composition partner (one minting under a disjoint
prefix) satisfy it vacuously.  Instantiating `Q := String.HasUnderscoreDigitSuffix`
recovers the blanket `hoistLoopPrefixInits_preserves`. -/
theorem hoistLoopPrefixInits_preserves_kind {Q : String → Prop}
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {extendEval : ExtendEval P}
    (ss : List (Stmt P (Cmd P)))
    {ρ_src ρ_src' : Env P}
    (h_no_nd      : Block.containsNondetLoop ss = false)
    (h_no_fd      : Block.containsFuncDecl ss = false)
    (h_no_inv     : Block.loopHasNoInvariants ss = true)
    (h_no_measure : Block.loopMeasureNone ss = true)
    (h_exprs_shapefree : Block.exprsShapeFree (P := P) Q ss)
    (h_unique     : Block.uniqueInits ss)
    (h_fresh      : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss = true)
    (h_src_initVars_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars ss)
    (h_src_modifiedVars_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.modifiedVars ss)
    (h_hoist_undef : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_src_store_shapefree :
      ∀ str : String, Q str →
        ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendEval
                       (.stmts ss ρ_src) (.terminal ρ_src'))
    (h_wfvar      : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr    : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst    : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef      : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    ∃ ρ_h',
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.hoistLoopPrefixInits ss) ρ_src) (.terminal ρ_h')
      ∧ StoreAgreement ρ_src'.store ρ_h'.store
      ∧ ρ_h'.hasFailure = ρ_src'.hasFailure := by
  -- Discharge §F by invoking the widened §E Block sibling at `A := []`, `B := []`,
  -- `subst := []`, `σ := emp`, with `ρ_hoist := ρ_src` (no hoisting at the
  -- outermost call site).  The σ-relative obligations collapse at `emp` (its
  -- `stringGens` is empty) to the global front-end kind-freedom facts.
  -- The §E Block sibling's separate `h_names_fresh A`/`h_names_fresh_B` slots take
  -- the FULL `namesFreshInExprs` (where the guard clause is load-bearing) at the
  -- hoist-accumulated names `A`/`B`; at the outermost call site `A = B = []`, so
  -- they are vacuously true and need no input from `h_fresh`.
  have h_names_fresh_nil : Block.namesFreshInExprs (P := P) [] ss = true :=
    Block.namesFreshInExprs_nil ss
  have h_lhs_disjoint_nil : ∀ y ∈ Block.initVars (P := P) ss, y ∉ ([] : List P.Ident) :=
    fun _ _ => List.not_mem_nil
  have h_mod_disjoint_nil : ∀ x ∈ Block.modifiedVars (P := P) (C := Cmd P) ss, x ∉ ([] : List P.Ident) :=
    fun _ _ => List.not_mem_nil
  have h_hinv_refl : HoistInv (P := P) [] [] [] ρ_src.store ρ_src.store :=
    HoistInv.refl_id [] ρ_src.store
  have h_hoist_bound_nil : ∀ y ∈ ([] : List P.Ident), ρ_src.store y ≠ none :=
    fun _ h => absurd h (List.not_mem_nil)
  have h_wf_emp : StringGenState.WF StringGenState.emp := StringGenState.wf_emp
  have h_src_fresh_emp :
      ∀ str ∈ StringGenState.stringGens StringGenState.emp,
        HasIdent.ident (P := P) str ∉ ([] : List P.Ident) ∧
        HasIdent.ident (P := P) str ∉ ([] : List P.Ident) ∧
        HasIdent.ident (P := P) str ∉ Block.initVars (P := P) ss := by
    intro str h_str
    exact absurd h_str (StringGenState.not_mem_stringGens_emp str)
  have h_src_shapefree_F :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ ([] : List P.Ident) ∧
        HasIdent.ident (P := P) str ∉ ([] : List P.Ident) ∧
        HasIdent.ident (P := P) str ∉ Block.initVars (P := P) ss ∧
        HasIdent.ident (P := P) str ∉ Block.modifiedVars (P := P) ss :=
    fun str h_shape =>
      ⟨List.not_mem_nil, List.not_mem_nil, h_src_initVars_shapefree str h_shape,
        h_src_modifiedVars_shapefree str h_shape⟩
  have h_subst_wf_nil :
      ∀ a b : P.Ident, (a, b) ∈ ([] : List (P.Ident × P.Ident)) → a ∈ ([] : List P.Ident) ∧ b ∈ ([] : List P.Ident) :=
    fun _ _ h => absurd h List.not_mem_nil
  have h_src_store_shapefree_emp :
      ∀ str : String, Q str →
        str ∉ StringGenState.stringGens StringGenState.emp →
        ρ_src.store (HasIdent.ident (P := P) str) = none :=
    fun str h_shape _ => h_src_store_shapefree str h_shape
  obtain ⟨ρ_h', cfg_hoist, h_run_h, h_disj⟩ :=
    Block.hoistLoopPrefixInits_preserves hQmint (extendEval := extendEval) [] [] [] ss
      StringGenState.emp
      h_no_nd h_no_fd h_no_inv h_no_measure h_exprs_shapefree h_unique h_fresh
      h_names_fresh_nil h_names_fresh_nil h_lhs_disjoint_nil h_lhs_disjoint_nil
      h_mod_disjoint_nil h_mod_disjoint_nil
      h_hoist_undef h_hoist_undef h_src_store_shapefree_emp h_src_store_shapefree_emp
      h_wf_emp h_src_fresh_emp h_src_shapefree_F h_subst_wf_nil
      h_hinv_refl rfl rfl h_hoist_bound_nil
      h_run_src (Or.inl ⟨ρ_src', rfl⟩) h_wfvar h_wfcongr h_wfsubst h_wfdef
  rcases h_disj with
    ⟨ρ_src'', h_eq_src, h_eq_hoist, h_hinv_final, h_hf_final, _⟩
    | ⟨_, _, h_eq_src_e, _⟩
  · cases h_eq_src
    subst h_eq_hoist
    exact ⟨ρ_h', h_run_h, HoistInv.to_storeAgreement_nil h_hinv_final, h_hf_final.symm⟩
  · exact absurd h_eq_src_e (by simp)

/-! ## §F — Top-level forward-simulation theorem

Stated with full Phase 8 signature. The proof is a direct invocation of the
§E Block-level mutual sibling `Block.hoistLoopPrefixInits_preserves` at
`cfg_src := .terminal ρ_src'`. The §E mutual is fully discharged (every arm,
including `.loop`), so §F is unconditionally discharged. -/

/-- Phase 8 top-level theorem: `Block.hoistLoopPrefixInits` is a forward
simulation. Every terminating source run admits a corresponding terminating
hoisted run that produces a pointwise-equal final store and the same
`hasFailure` flag.

Preconditions (front-end shape, all already enforced upstream of the
hoisting pass entry):
* `h_no_nd`     — no `.loop _ .nondet ...` anywhere
* `h_no_fd`     — no `.funcDecl ...` anywhere
* `h_no_inv`    — no `.loop` carries a non-empty `invariants` list
* `h_no_measure` — no `.loop` carries an explicit termination measure
* `h_unique`    — `.init` LHS uniqueness across the program
* `h_fresh`     — hoisted names are fresh in every guard and RHS expression
                   they would be moved past
* `h_src_initVars_shapefree` — no `.init` LHS name is the image (under
                   `HasIdent.ident`) of a string carrying the generator's
                   `_<digits>` suffix shape. This is the legitimate front-end
                   well-formedness assumption that source identifiers never
                   collide with the freshly-minted names the hoisting pass's
                   string generator produces; it discharges the §E
                   `h_src_shapefree` obligation at the `A = B = []` entry.
* `h_src_modifiedVars_shapefree` — no `.set` LHS name (the source program's
                   modified vars) is the image of a suffix-shaped string.  Same
                   front-end well-formedness class as `h_src_initVars_shapefree`:
                   a source `set _hoist_0 := …` would collide with a generated
                   loop-rename target and miscompile.  Used by the `.loop` arm's
                   `modifiedVars body₁ ∩ targetsOf' E = ∅` obligation.
* `h_hoist_undef` — every name introduced by an `.init` (and therefore
                   eligible for hoisting) is unbound in `ρ_src`. This is
                   the runtime-shape precondition consumed by the §E
                   `.loop` arm via `prelude_execution`.

Plus two semantic well-formedness preconditions for the underlying step
relation (matching the LoopInitHoistInfra convention):
* `h_wfvar`     — every environment's `eval` respects variable extension
* `h_wfcongr`   — every environment's `eval` respects congruence under
                   pointwise store equality.

Conclusion: there exists a hoisted-side terminating run whose store agrees
with the source store on every source-defined variable (`StoreAgreement`,
i.e. semantics preservation modulo the freshly-hoisted variables) and which
carries the same `hasFailure` value. Exact pointwise equality does NOT hold
in general — the hoisting pass introduces fresh `_hoist`-suffixed targets
that are defined only in the hoisted store.

**Status:** discharged via the §E Block-IH at `cfg_src := .terminal ρ_src'`,
projecting the terminal disjunct of the sum-typed conclusion. The §E mutual
is fully discharged (every arm, including `.loop`), so §F is unconditionally
discharged. -/
theorem hoistLoopPrefixInits_preserves
    [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    (ss : List (Stmt P (Cmd P)))
    {ρ_src ρ_src' : Env P}
    (h_no_nd      : Block.containsNondetLoop ss = false)
    (h_no_fd      : Block.containsFuncDecl ss = false)
    (h_no_inv     : Block.loopHasNoInvariants ss = true)
    (h_no_measure : Block.loopMeasureNone ss = true)
    (h_exprs_shapefree : Block.exprsShapeFree (P := P) String.HasUnderscoreDigitSuffix ss)
    (h_unique     : Block.uniqueInits ss)
    (h_fresh      : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss = true)
    (h_src_initVars_shapefree :
      ∀ str : String, String.HasUnderscoreDigitSuffix str →
        HasIdent.ident (P := P) str ∉ Block.initVars ss)
    (h_src_modifiedVars_shapefree :
      ∀ str : String, String.HasUnderscoreDigitSuffix str →
        HasIdent.ident (P := P) str ∉ Block.modifiedVars ss)
    (h_hoist_undef : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_src_store_shapefree :
      ∀ str : String, String.HasUnderscoreDigitSuffix str →
        ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendEval
                       (.stmts ss ρ_src) (.terminal ρ_src'))
    (h_wfvar      : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr    : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst    : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef      : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    ∃ ρ_h',
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.hoistLoopPrefixInits ss) ρ_src) (.terminal ρ_h')
      ∧ StoreAgreement ρ_src'.store ρ_h'.store
      ∧ ρ_h'.hasFailure = ρ_src'.hasFailure :=
  -- The blanket statement is the `Q := String.HasUnderscoreDigitSuffix`
  -- instance of the kind-generalized `hoistLoopPrefixInits_preserves_kind`:
  -- the blanket "shape-free" hypotheses (no source name is the image of any
  -- gen-suffix-shaped string) are exactly that lemma's per-kind hypotheses at
  -- `Q := String.HasUnderscoreDigitSuffix`, and the mint witness `hQmint` is
  -- `StringGenState.gen_hasUnderscoreDigitSuffix` (every minted name is
  -- suffix-shaped).
  hoistLoopPrefixInits_preserves_kind
    (Q := String.HasUnderscoreDigitSuffix)
    (fun sg => StringGenState.gen_hasUnderscoreDigitSuffix hoistFreshPrefix sg)
    ss
    h_no_nd h_no_fd h_no_inv h_no_measure h_exprs_shapefree h_unique h_fresh
    h_src_initVars_shapefree h_src_modifiedVars_shapefree h_hoist_undef
    h_src_store_shapefree h_run_src h_wfvar h_wfcongr h_wfsubst h_wfdef

-- NOTE: the former `hoistLoopPrefixInits_preserves_funext` corollary (extensional
-- store equality `ρ_h'.store = ρ_src'.store`) is intentionally dropped: that
-- equality is FALSE for the hoisting pass, which introduces fresh hoist targets
-- defined only in the hoisted store. The sound relation is `StoreAgreement`
-- (preservation modulo hoisted variables), already concluded above.

end Imperative
