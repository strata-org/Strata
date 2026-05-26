/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.Tactics
public import Strata.Languages.Core.Procedure

public section

/-! # Provenance theorems for DECL/ASSIGN instructions

Close the provenance hypotheses that the v2 bridge in
`TranslatorBridgeHypsDischarge.lean` consumes:

* `decl_provenance_of_translator` — at every DECL PC, the GOTO code is
  `Code.decl (Expr.symbol (nameMap v_src) gty)` for some source-side
  identifier `v_src`.
* `assn_provenance_of_translator` — at every ASSIGN PC, the GOTO code is
  `Code.assign (Expr.symbol (nameMap v_src) gty) rhs_emitted` for some
  source-side identifier `v_src`, GOTO type `gty`, and emitted rhs.

## Strategy

`CmdEmittedAt` (in `CoreCFGToGOTOInvariants.lean`) exposes the exact
symbol shape in each constructor — `Expr.symbol (identToString v) gty`
for `init_det`, `init_nondet`, `set_det`, and `set_nondet`. Combined
with `WellFormedTranslation.layout_block_body`, every cmd in every
block admits a `CmdEmittedAt` witness whose constructors pin the GOTO
code shape.

The remaining work to derive the provenance theorems from `wf` alone
is the **CFG-PC inversion**: from a `pc` carrying a DECL/ASSIGN
instruction, find the block `(l, blk) ∈ cfg.blocks` and offset `k`
such that `pc = labelMap l + 1 + cmdsPrefixInstrCount blk.cmds k` (or
`+ 1` for the ASSIGN of an `init_det`).

This file's theorems hoist the inversion as an explicit hypothesis;
the proof of each is then a clean case-split on the `CmdEmittedAt`
constructors. -/

namespace CProverGOTO.CmdProvenance

open Imperative
open CProverGOTO

/-! ## DECL provenance

For any `pc` carrying a DECL instruction, the inversion gives a
`CmdEmittedAt pgm pc inner` witness whose constructor must be
`init_det` or `init_nondet` (those are the only constructors whose
relation-pc carries a DECL). Both constructors expose the symbol shape
via `h_decl_code`. -/

/-- Inversion hypothesis for DECL PCs: every DECL PC corresponds to
the cmd-start of an `init_*` cmd in some block of the CFG. The
relation `CmdEmittedAt pgm pc inner` indexes by the cmd-start PC, so
the DECL is at the relation-pc itself. -/
abbrev DeclPcInversion
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (_wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .DECL →
    ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner

/-- **DECL provenance**: at every DECL PC, the code's lhs is
`Expr.symbol (identToString v_src) gty` for some source-side `v_src`.

Discharged via case-analysis on the strengthened `CmdEmittedAt`
constructors. Only `init_det` and `init_nondet` admit a DECL at the
relation-pc; both expose the symbol shape via `h_decl_code`. The other
constructors (`set_det`, `set_nondet`, `assert_emit`, `assume_emit`,
`cover_emit`) all have `instr.type ≠ .DECL` at the relation-pc,
contradicting our hypothesis. -/
theorem decl_provenance_of_translator
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (h_inversion : DeclPcInversion cfg pgm δ δ_goto δ_goto_bool wf) :
    ∀ {pc : Nat} {instr : Instruction},
      pgm.instrAt pc = some instr → instr.type = .DECL →
      ∃ v_src gty,
        instr.code = Code.decl
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) := by
  intro pc instr h_at h_ty
  obtain ⟨inner, h_emit⟩ := h_inversion h_at h_ty
  cases h_emit with
  | init_det v _ty _e_core _md i_decl _i_assn h_decl_at _h_decl_ty
              _h_assn_at _h_assn_ty _e_goto gty h_decl_code _h_assn_code
              _h_translated =>
    -- `instr = i_decl` from `h_at` and `h_decl_at`.
    inj_subst h_at h_decl_at
    exact ⟨v, gty, h_decl_code⟩
  | init_nondet v _ty _md i_decl h_decl_at _h_decl_ty gty h_decl_code =>
    inj_subst h_at h_decl_at
    exact ⟨v, gty, h_decl_code⟩
  | set_det _v _e_core _md i_assn h_assn_at h_assn_ty _e_goto _gty
            _h_assn_code _h_translated =>
    -- Contradiction: instr.type = .DECL but h_assn_ty : i_assn.type = .ASSIGN.
    inj_subst h_at h_assn_at
    rw [h_assn_ty] at h_ty
    cases h_ty
  | set_nondet _v _md i_assn h_assn_at h_assn_ty _gty _h_assn_code =>
    inj_subst h_at h_assn_at
    rw [h_assn_ty] at h_ty
    cases h_ty
  | assert_emit _label _e_core _md i h_at_assert h_ty_assert _e_goto
                _h_guard _h_translated =>
    inj_subst h_at h_at_assert
    rw [h_ty_assert] at h_ty
    cases h_ty
  | assume_emit _label _e_core _md i h_at_assume h_ty_assume _e_goto
                _h_guard _h_translated =>
    inj_subst h_at h_at_assume
    rw [h_ty_assume] at h_ty
    cases h_ty
  | cover_emit _label _e_core _md i h_at_cover h_ty_cover _e_goto
                _h_guard _h_translated =>
    inj_subst h_at h_at_cover
    rw [h_ty_cover] at h_ty
    cases h_ty

/-! ## ASSIGN provenance

For any `pc` carrying an ASSIGN instruction, three constructor cases
match:

* `init_det` at relation-pc `pc - 1`, with the ASSIGN at `pc - 1 + 1 = pc`.
* `set_det` at relation-pc `pc`, with the ASSIGN at `pc`.
* `set_nondet` at relation-pc `pc`, with the ASSIGN at `pc`.

The inversion hypothesis must distinguish these. We use a strict
disjunction:

* offset-0 case: cmd-start = `pc`, with the cmd shape constrained to
  `set _ _ _` (so the constructor is `set_det`/`set_nondet`).
* offset-1 case: cmd-start = `pc - 1`, with the cmd shape constrained
  to `init _ _ (.det _) _` (so the constructor is `init_det`).

This shape is closable from the actual translator output: the
translator emits ASSIGN instructions only at offset 0 of `set_*` cmds
and offset 1 of `init_det` cmds. -/

/-- Inversion hypothesis for ASSIGN PCs: an ASSIGN at PC is either
the start-instruction of a `set _ _ _` cmd, or the second instruction
of an `init _ _ (.det _) _` cmd at PC - 1. -/
abbrev AssignPcInversion
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (_wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .ASSIGN →
    -- offset-0 (set case)
    (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v cv md)) ∨
    -- offset-1 (init_det case)
    (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
      CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
        (.init v ty (.det e_core) md))

/-- **ASSIGN provenance**: at every ASSIGN PC, the code's lhs is
`Expr.symbol (identToString v_src) gty` for some source-side `v_src`,
with arbitrary emitted rhs.

Discharged via case-analysis on the inversion's two branches:

* offset-0: the cmd is `.set v cv md` for some `cv`, matched by
  `set_det` (when `cv = .det e`) or `set_nondet` (when `cv = .nondet`).
  Both expose the symbol shape via `h_assn_code`.
* offset-1: the cmd is `.init v ty (.det e) md`, matched by
  `init_det`. Its `h_assn_code` exposes the symbol shape with the
  ASSIGN at `pc_pred + 1 = pc`. -/
theorem assn_provenance_of_translator
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (h_inversion : AssignPcInversion cfg pgm δ δ_goto δ_goto_bool wf) :
    ∀ {pc : Nat} {instr : Instruction},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      ∃ v_src gty rhs_emitted,
        instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty)
          rhs_emitted := by
  intro pc instr h_at h_ty
  rcases h_inversion h_at h_ty with
    ⟨v, cv, md, h_emit⟩ | ⟨pc_pred, v, ty, e_core, md, h_pc_eq, h_emit⟩
  · -- offset-0 case: cmd is `.set v cv md`.
    -- Inner case-split on cv: .det or .nondet.
    cases cv with
    | det e_core =>
      -- The CmdEmittedAt for `.set v (.det e_core) md` must be `set_det`.
      cases h_emit with
      | set_det _ _ _ i_assn h_assn_at _h_assn_ty e_goto gty
                h_assn_code _h_translated =>
        inj_subst h_at h_assn_at
        exact ⟨v, gty, e_goto, h_assn_code⟩
    | nondet =>
      -- The CmdEmittedAt for `.set v .nondet md` must be `set_nondet`.
      cases h_emit with
      | set_nondet _ _ i_assn h_assn_at _h_assn_ty gty h_assn_code =>
        inj_subst h_at h_assn_at
        obtain ⟨e_nondet, h_code, _h_id, _h_ty_eq⟩ := h_assn_code
        exact ⟨v, gty, e_nondet, h_code⟩
  · -- offset-1 case: cmd is `.init v ty (.det e_core) md`, ASSIGN at pc_pred + 1.
    subst h_pc_eq
    cases h_emit with
    | init_det _ _ _ _ _i_decl i_assn _h_decl_at _h_decl_ty
                h_assn_at _h_assn_ty e_goto gty _h_decl_code h_assn_code
                _h_translated =>
      inj_subst h_at h_assn_at
      exact ⟨v, gty, e_goto, h_assn_code⟩

end CProverGOTO.CmdProvenance
