/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.Passive.Program
public import Strata.Transform.Passive.LangProps
public import Strata.Transform.Passive.Eval
import Strata.Util.ExceptProps

/-! # Simulation vocabulary for the WP phase

The definitions the correctness proof of the pass relates a loop-free run and an
obligation-program run with:

* runs of a flat translation along its straight-line items (`MainRun`) and into a side
  branch (`HitIn`);
* the truth of reachability conditions in an obligation store (`RE.Holds`, `RE.Fails`);
* the relation between a loop-free store and an obligation store at a program point
  (`Rel`), and a failing feasible trace (`BigStep.Claim`) refined by the kind of its failing
  event (`ClaimK`).

Key definitions: `MainRun`, `HitIn`, `Rel`, `ClaimK`, `RE.Holds`, `RE.Fails`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iDE iB iLB iBo iFv iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

/-! ## Runs of flat translations -/

/-- A run of the straight-line items of a flat translation: plain items execute, side
    branches are skipped (the run continues on the `else` of their `ite`); no run passes a
    real branch. -/
inductive MainRun (F : P.Factory) : List (Item P) → SemanticStore P →
    List (Event P) → SemanticStore P → Prop where
  | nil : MainRun F [] σ [] σ
  | plain : EvalE F σ c σ1 evs1 → MainRun F rest σ1 evs2 σ2 →
      MainRun F (.plain (.cmd c) :: rest) σ (evs1 ++ evs2) σ2
  | side : MainRun F rest σ evs σ2 → MainRun F (.obls r cs :: rest) σ evs σ2

/-- A run of a flat translation that stops inside a side branch, or inside an arm of a real
    branch. -/
inductive HitIn (F : P.Factory) : List (Item P) → SemanticStore P →
    List (Event P) → Prop where
  | here : BReach F (reachPre r ++ cs) σ evs → HitIn F (.obls r cs :: rest) σ evs
  | plain : EvalE F σ c σ1 evs1 → HitIn F rest σ1 evs2 →
      HitIn F (.plain (.cmd c) :: rest) σ (evs1 ++ evs2)
  | side : HitIn F rest σ evs → HitIn F (.obls r cs :: rest) σ evs
  | branchT : HitIn F t σ evs → HitIn F (.branch t e :: rest) σ evs
  | branchE : HitIn F e σ evs → HitIn F (.branch t e :: rest) σ evs

/-! ## The simulation relation

The truth of reachability conditions, the relation between the loop-free and obligation
stores, and failing traces. -/

/-- A reachability condition holds in the obligation store. -/
@[expose] def RE.Holds (F : P.Factory) (σ : SemanticStore P) : RE P → Prop
  | .top => True
  | .name r => σ r = some (HasBool.ttVal F)
  | .neg g => σ g = some (HasBool.ffVal F)
  | .andNeg q g => σ q = some (HasBool.ttVal F) ∧ σ g = some (HasBool.ffVal F)

/-- A reachability condition is false in the obligation store. -/
@[expose] def RE.Fails (F : P.Factory) (σ : SemanticStore P) : RE P → Prop
  | .top => False
  | .name r => σ r = some (HasBool.ffVal F)
  | .neg g => σ g = some (HasBool.ttVal F)
  | .andNeg q g => (σ q = some (HasBool.ffVal F) ∧ (σ g).isSome) ∨
    (σ q = some (HasBool.ttVal F) ∧ σ g = some (HasBool.ttVal F))

/-- The loop-free store `σ` and the obligation store `σ'` at a program point: on the
    variables `S` in scope that the continuation reads (`V`), `σ` is defined and agrees
    with `σ'` through `ρ`; a local out of scope is undefined in `σ`; both stores hold
    values. -/
structure Rel (F : P.Factory) (Lc : List P.Ident) (ρ : (Ren P)) (S V : List P.Ident)
    (σ σ' : SemanticStore P) : Prop where
  agree : ∀ x ∈ S, x ∈ V → σ x = σ' (ρ.get x) ∧ (σ x).isSome
  undef : ∀ x ∈ Lc, x ∉ S → σ x = none
  canon : WellFormedStore σ F
  canon' : WellFormedStore σ' F

/-- A trace reaching a failing occurrence of `t` with the condition `e` on a feasible path
    (`Claim`) at an event of kind `k`: a cover when `k` is `true`, an assertion when `k` is
    `false`. -/
@[expose] def ClaimK (k : Bool) (t : AssertId P) (e : P.Expr) (tr : List (Event P)) : Prop :=
  ∃ evs a, tr = evs ++ [if k then .cover a else .assert a] ∧
    Trace.AssumptionsHold P evalInterp () evs ∧ FailsAt t e (if k then .cover a else .assert a) ∧
    a.expr = e

end -- public section

end WP
end Imperative
