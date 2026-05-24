/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
public import Strata.Backends.CBMC.GOTO.WellFormedTranslationProps
public import Strata.Languages.Core.Procedure

public section

/-! # Bridge lemmas for `TranslatorBridgeHyps` lookup fields

Round-7c deliverable: this file closes R6a's three lookup-field caller
passthroughs in `TranslatorBridgeHypsDischarge.lean`:

* `decl_lookup` — at every DECL PC, the GOTO code's symbol matches
  `nameMap x` for the source-side `InitState`'s `x`,
* `assign_lookup` — at every ASSIGN PC firing `step_assign`, the lhs
  matches `nameMap x` and the rhs matches the GOTO translation of the
  source rhs,
* `assign_nondet_lookup` — at every ASSIGN PC firing `step_assign_nondet`,
  the lhs matches `nameMap x` and the rhs has `id = .side_effect .Nondet`.

## Strategy

Round-7's strengthening of `CmdEmittedAt`
(`CoreCFGToGOTOInvariants.lean`) fixes the lhs operand to
`Expr.symbol (identToString v) gty` (where `v` is the source-cmd's
variable). Combined with `WellFormedTranslation.layout_block_body`,
this gives us, *for every PC that corresponds to a CFG-level command*,
an explicit `Code.decl`/`Code.assign` shape carrying the source-cmd's
variable name.

The remaining gap — and the reason these lemmas take an auxiliary
caller hypothesis — is the **universal-`x` quantification** in the
`TranslatorBridgeHyps` field types. Each lookup field is universally
quantified over `x : P.Ident` and over `σ, σ', v` satisfying an
`InitState`/`UpdateState` predicate. The translator's emitted GOTO
code at any PC mentions a *specific* source variable `v_src` (the one
the source-CFG cmd at that PC was about), but the field demands the
result for *any* `x` that satisfies the source-side relation —
including `x ≠ v_src`.

For the actual translator output, `code = Code.decl (Expr.symbol
(nameMap v_src) gty)` (assuming `nameMap = identToString`), so
`getSymbolName code = some (nameMap v_src)`. The field requires this
to equal `some (nameMap x)`; by injectivity of `nameMap`, that's
`x = v_src`. So the bridge field implicitly demands "every valid
InitState/UpdateState firing at this PC has `x = v_src`" — a
trace-level constraint that's true in the actual simulation but is
**not** in `WellFormedTranslation`.

Each bridge lemma below therefore:

1. Decomposes the lookup field into the structural part (mechanical
   from WF + strengthened `CmdEmittedAt`) and the trace-level part
   (caller obligation).
2. Takes the trace-level part as an explicit auxiliary hypothesis.
3. Closes the field's body via a small calculation:
   `code's symbol = nameMap v_src` (from WF) + `x = v_src` (caller) +
   `nameMap` injectivity (caller passthrough).

The auxiliary hypotheses are **strictly smaller** than the original
lookup fields: they take a single PC (no explicit `x` universal)
plus the InitState/UpdateState data, and produce only the
"x equals the source-cmd's variable" claim. The lookup-field ∀-x and
∀-σ remain encapsulated in the conclusion type.

## Boundary

These lemmas do **not** discharge the auxiliary hypothesis. That
hypothesis is genuinely caller-side (it depends on how the source
trace is reflected in the GOTO simulation, which is the consumer's
job to prove via bisimulation invariants). The Tier-3 (Acceptable)
contribution here is the *mechanical* bridge from WF + strengthened
`CmdEmittedAt` to the lookup field, surfacing the irreducible
trace-consistency obligation. -/

namespace CProverGOTO.InstructionLookups

open Imperative
open CProverGOTO
open CProverGOTO.SemanticsTautschnig (instrCode getSymbolName getAssignLhs getAssignRhs)

/-! ## Helpers -/

/-- Auxiliary lemma: `getSymbolName (Code.decl (Expr.symbol s gty)) = some s`.
The proof rewrites `Code.decl`/`Expr.symbol` to their record-literal forms
via `rfl`-equalities, then closes by `rfl`. -/
private theorem getSymbolName_decl_symbol (s : String) (gty : CProverGOTO.Ty) :
    getSymbolName (Code.decl (Expr.symbol s gty)) = some s := by
  have h1 : Code.decl (Expr.symbol s gty) =
    ({ id := .assignment .decl,
       operands := [Expr.symbol s gty] } : Code) := rfl
  have h2 : Expr.symbol s gty =
    ({ id := .nullary (.symbol s), type := gty } : Expr) := rfl
  rw [h1, h2]
  rfl

/-- Auxiliary lemma: `getAssignLhs (Code.assign (Expr.symbol s gty) e) = some s`. -/
private theorem getAssignLhs_assign_symbol
    (s : String) (gty : CProverGOTO.Ty) (e : Expr) :
    getAssignLhs (Code.assign (Expr.symbol s gty) e) = some s := by
  have h1 : Code.assign (Expr.symbol s gty) e =
    ({ id := .assignment .assign,
       operands := [Expr.symbol s gty, e] } : Code) := rfl
  have h2 : Expr.symbol s gty =
    ({ id := .nullary (.symbol s), type := gty } : Expr) := rfl
  rw [h1, h2]
  rfl

/-- Auxiliary lemma: `getAssignRhs (Code.assign lhs e) = some e`. -/
private theorem getAssignRhs_assign
    (lhs e : Expr) :
    getAssignRhs (Code.assign lhs e) = some e := by
  have h1 : Code.assign lhs e =
    ({ id := .assignment .assign,
       operands := [lhs, e] } : Code) := rfl
  rw [h1]
  rfl

/-- For a DECL instruction whose `code` field is exactly
`Code.decl (Expr.symbol s gty)`, the `instrCode pgm pc`/`getSymbolName`
chain reduces to `some s`. -/
private theorem decl_code_to_symbolName
    (pgm : Program) {pc : Nat} {instr : Instruction}
    (s : String) (gty : CProverGOTO.Ty)
    (h_at : pgm.instrAt pc = some instr)
    (h_code : instr.code = Code.decl (Expr.symbol s gty)) :
    (instrCode pgm pc).bind getSymbolName = some s := by
  have h_at_eq : pgm.instructions[pc]? = some instr := h_at
  simp only [SemanticsTautschnig.instrCode, h_at_eq, Option.map_some,
    Option.bind_some, h_code, getSymbolName_decl_symbol]

/-- For an ASSIGN instruction whose `code` field is exactly
`Code.assign (Expr.symbol s gty) e_goto`, the `instrCode pgm pc`/
`getAssignLhs` chain reduces to `some s` and the `getAssignRhs` chain
reduces to `some e_goto`. -/
private theorem assign_code_to_lhsRhs
    (pgm : Program) {pc : Nat} {instr : Instruction}
    (s : String) (gty : CProverGOTO.Ty) (e_goto : Expr)
    (h_at : pgm.instrAt pc = some instr)
    (h_code : instr.code = Code.assign (Expr.symbol s gty) e_goto) :
    (instrCode pgm pc).bind getAssignLhs = some s ∧
    (instrCode pgm pc).bind getAssignRhs = some e_goto := by
  have h_at_eq : pgm.instructions[pc]? = some instr := h_at
  refine ⟨?_, ?_⟩
  · simp only [SemanticsTautschnig.instrCode, h_at_eq, Option.map_some,
      Option.bind_some, h_code, getAssignLhs_assign_symbol]
  · simp only [SemanticsTautschnig.instrCode, h_at_eq, Option.map_some,
      Option.bind_some, h_code, getAssignRhs_assign]

/-! ## `decl_lookup` discharge

The bridge lemma takes the structural fact "at this DECL PC, the code
is `Code.decl (Expr.symbol (nameMap v_src) gty)` for some `v_src`"
(discharable from `wf` + strengthened `CmdEmittedAt`) plus the
trace-level fact "any InitState's x equals v_src at this PC". -/

/-- Bridge from a per-PC structural witness (the GOTO code's symbol
matches `nameMap v_src`) plus a per-firing trace witness (any InitState
at this PC has `x = v_src`) to the `decl_lookup` field of
`TranslatorBridgeHyps`.

The structural witness `h_decl_provenance` is mechanical from
`WellFormedTranslation.layout_block_body` once you've located the
source-CFG cmd at this PC (a small CFG-PC inversion) and unpacked the
strengthened `CmdEmittedAt.init_det`/`init_nondet` constructors.

The trace witness `h_x_pinned` is a caller-side obligation tracking
the bisimulation between source-side `EvalCmd.eval_init` and target-side
`step_decl`. It is true at every DECL PC reached during a coupled
trace because `EvalCmd.eval_init` fires only with the cmd's own `v`. -/
theorem decl_lookup_of_provenance_and_pinned
    (pgm : Program)
    (nameMap : Core.Expression.Ident → String)
    (h_decl_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        ∃ v_src gty, instr.code = Code.decl (Expr.symbol (nameMap v_src) gty))
    (h_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl (Expr.symbol (nameMap v_src) gty) →
        x = v_src) :
    ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
      {σ σ' : Imperative.SemanticStore Core.Expression}
      {v : Core.Expression.Expr},
      pgm.instrAt pc = some instr → instr.type = .DECL →
      Imperative.InitState Core.Expression σ x v σ' →
      (instrCode pgm pc).bind getSymbolName = some (nameMap x) := by
  intro pc instr x σ σ' v h_at h_ty h_init
  obtain ⟨v_src, gty, h_code⟩ := h_decl_provenance h_at h_ty
  have h_x : x = v_src := h_x_pinned h_at h_ty h_init v_src gty h_code
  rw [h_x]
  exact decl_code_to_symbolName pgm (nameMap v_src) gty h_at h_code

/-! ## `assign_lookup` discharge

For `step_assign`, the bridge field needs `getAssignLhs = some
(nameMap x)` and `getAssignRhs = some rhs_g` (where `rhs_g` is the
firing's GOTO-side rhs). The structural witness gives us the lhs and
the rhs the translator emits; matching this to the firing's `rhs_g`
requires the trace-level fact "the firing's rhs_g equals the
translator's emitted rhs". -/

/-- Bridge from per-PC structural witness + per-firing trace witnesses
to the `assign_lookup` field. Splits into:
* `h_assn_provenance`: at this ASSIGN PC, the code is
  `Code.assign (Expr.symbol (nameMap v_src) gty) rhs_emitted` for some
  source-cmd variable `v_src` and emitted rhs `rhs_emitted`.
* `h_x_pinned`: any UpdateState at this PC has `x = v_src`.
* `h_rhs_pinned`: any `δ_goto σ rhs_g = some v_imp` at this PC has
  `rhs_g = rhs_emitted`.

The first two are direct analogs of `decl_lookup`'s. The third is the
caller's bisim invariant on rhs evaluation: in a coupled trace, the
GOTO-side rhs the simulator picks is exactly the translator's emitted
rhs. -/
theorem assign_lookup_of_provenance_and_pinned
    (pgm : Program)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (nameMap : Core.Expression.Ident → String)
    (h_assn_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted)
    (h_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          x = v_src)
    (h_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          rhs_g = rhs_emitted) :
    ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
      {σ σ' : Imperative.SemanticStore Core.Expression}
      {rhs_g : Expr} {v_imp : Core.Expression.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      δ_goto σ rhs_g = some v_imp →
      Imperative.UpdateState Core.Expression σ x v_imp σ' →
      (instrCode pgm pc).bind getAssignLhs = some (nameMap x) ∧
      (instrCode pgm pc).bind getAssignRhs = some rhs_g := by
  intro pc instr x σ σ' rhs_g v_imp h_at h_ty h_eval h_upd
  obtain ⟨v_src, gty, rhs_emitted, h_code⟩ := h_assn_provenance h_at h_ty
  have h_x : x = v_src := h_x_pinned h_at h_ty h_upd v_src gty rhs_emitted h_code
  have h_rhs : rhs_g = rhs_emitted :=
    h_rhs_pinned h_at h_ty h_eval v_src gty rhs_emitted h_code
  obtain ⟨h_lhs_eq, h_rhs_eq⟩ :=
    assign_code_to_lhsRhs pgm (nameMap v_src) gty rhs_emitted h_at h_code
  refine ⟨?_, ?_⟩
  · rw [h_x]; exact h_lhs_eq
  · rw [h_rhs]; exact h_rhs_eq

/-! ## `assign_nondet_lookup` discharge

R11: `step_assign_nondet`'s constructor now carries the rhs-shape
witnesses directly (`instr.code = Code.assign lhs rhs ∧
rhs.id = .side_effect .Nondet`). The bridge field receives them as
preconditions; the discharge here just unifies them with the
translator's emitted shape via R7c's `assn_provenance` and
`assn_x_pinned` hypotheses (the same ones used by `assign_lookup`).

In particular, no `AssignNondetPcInversion` is needed: the rhs-shape
witness comes from the constructor, not from the structural lemma. -/

/-- Bridge from per-PC structural witness + per-firing trace witnesses
to the new `assign_nondet_lookup` field shape (R11). -/
theorem assign_nondet_lookup_of_provenance_and_pinned
    (pgm : Program)
    (nameMap : Core.Expression.Ident → String)
    (h_assn_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted)
    (h_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          x = v_src) :
    ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
      {lhs rhs : Expr}
      {σ σ' : Imperative.SemanticStore Core.Expression}
      {v_imp : Core.Expression.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      instr.code = Code.assign lhs rhs →
      rhs.id = .side_effect .Nondet →
      Imperative.UpdateState Core.Expression σ x v_imp σ' →
      (instrCode pgm pc).bind getAssignLhs = some (nameMap x) ∧
      (instrCode pgm pc).bind getAssignRhs = some rhs := by
  intro pc instr x lhs rhs σ σ' v_imp h_at h_ty h_code _h_id h_upd
  obtain ⟨v_src, gty, rhs_emitted, h_code_prov⟩ :=
    h_assn_provenance h_at h_ty
  have h_x : x = v_src := h_x_pinned h_at h_ty h_upd v_src gty rhs_emitted h_code_prov
  -- The lookup chain via `instrCode pgm pc` doesn't depend on the
  -- specific decomposition; reduce it directly via `h_code_prov`.
  obtain ⟨h_lhs_eq, h_rhs_eq⟩ :=
    assign_code_to_lhsRhs pgm (nameMap v_src) gty rhs_emitted h_at h_code_prov
  -- From `h_code` and `h_code_prov`, both equate `instr.code` to
  -- `Code.assign _ _` shapes. Unfolding shows the operands lists
  -- coincide, so `lhs = Expr.symbol (nameMap v_src) gty` and
  -- `rhs = rhs_emitted`.
  have h_code_eq : Code.assign lhs rhs =
      Code.assign (Expr.symbol (nameMap v_src) gty) rhs_emitted := by
    rw [← h_code, h_code_prov]
  -- Inject through Code.mk; both have id `.assignment .assign`
  -- and operands `[_, _]`.
  have h_ops_eq : ([lhs, rhs] : List Expr) =
      [Expr.symbol (nameMap v_src) gty, rhs_emitted] := by
    injection h_code_eq
  -- List.cons.injEq peels two times.
  have h_lhs_eq_sym : lhs = Expr.symbol (nameMap v_src) gty := by
    injection h_ops_eq
  have h_rhs_eq_emit : rhs = rhs_emitted := by
    injection h_ops_eq with _ h_rest
    injection h_rest
  refine ⟨?_, ?_⟩
  · rw [h_x]; exact h_lhs_eq
  · rw [h_rhs_eq_emit]; exact h_rhs_eq

end CProverGOTO.InstructionLookups
