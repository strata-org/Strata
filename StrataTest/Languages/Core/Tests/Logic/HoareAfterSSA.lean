/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.SSA.SSACoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterSSATest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `growBody` spells out with `loc`, so an edit above it
    moves them. -/
private def growPgm : Program :=
#strata
program Core;

procedure Grow(x : int, out y : int)
{
  y := int.add(x, 1);
  y := int.add(y, y);
  assert [grow]: int.gt(y, x);
};
#end

private def growPgmAST : Core.Program := cstToAST growPgm

private abbrev π : String → Option Core.Procedure := growPgmAST.findProcByString?

/-! # An assertion proved on the static-single-assignment form

```
procedure Grow(x : int, out y : int)
{
  y := int.add(x, 1);
  y := int.add(y, y);
  assert [grow]: int.gt(y, x);
}
```

The SSA phase (`Core.WP.ssaLoopFree`) reads the parameters under entry names and gives each
assignment a fresh name, defined once:

```
var y@2 : int := int.add(x@0, 1);
var y@3 : int := int.add(y@2, y@2);
assert [grow]: int.gt(y@3, x@0);
```

where `x@0` and `y@1` are the entry names of `x` and `y`.  The `init` and assertion rules prove
that, from an entry where `x@0` holds a non-negative integer, `grow` holds on every completed
run.  `Core.WP.ssa_triple` carries that back to the original body, from every entry where `x`
holds a non-negative integer and `y` an integer: such an entry has an entry of the output
holding the same values under the entry names (`SSAEntryRel`, built by `entryEnv`).  The
final stores of the two bodies are not related, so the postcondition is `True`: the triple
says that every assertion of the body holds on its completed runs.

The translated body is spelled out as the closed term `growBody`.  The facts that bind the
translated program to it (`grow_body_eq`, and the facts about the parameters `xs_eq`, `al_eq`,
`tys_x`, `tys_y`) use `native_decide`: the translation is `partial`, so the kernel cannot
reduce it.  So do the facts about the output of the SSA phase (`grow_run`, `grow_ssa`, `ren_x`,
`ren_y`): the phase keeps its renaming and the names to avoid in `Std.HashMap`s and
`Std.HashSet`s, which the kernel cannot reduce.  `grow_freeVars` uses `native_decide` too: the
kernel gets stuck on the free variables of the expressions (`exprFV`).
-/

private def growProc : Core.Procedure := (π "Grow").get!

private def xId : Core.Expression.Ident := ⟨"x", ()⟩
private def yId : Core.Expression.Ident := ⟨"y", ()⟩

/-- The metadata of the assertion: its source location and its label as the property summary. -/
private abbrev assertMd : MetaData Core.Expression :=
  (loc 642 670).push ⟨.label "propertySummary", .msg "grow"⟩

/-- `int.add(a, b)` of two variables or a variable and a literal. -/
private abbrev addE (a b : Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () Core.intAddOp a) b

/-- The translated body. -/
private abbrev growBody : Core.Statements :=
  [Core.Statement.set yId (addE (v xId) (.intConst () 1)) (loc 598 617),
   Core.Statement.set yId (addE (v yId) (v yId)) (loc 620 639),
   Core.Statement.assert "grow" (.app () (.app () Core.intGtOp (v yId)) (v xId)) assertMd]

/-- The translated body really is the two assignments followed by the assertion. -/
private theorem grow_body_eq : growProc.body = .structured growBody := by native_decide

/-! ## The SSA form -/

/-- The entry names of `x` and `y`, and the fresh names of the two assignments. -/
private def x0 : Core.Expression.Ident := ⟨"x@0", ()⟩
private def y1 : Core.Expression.Ident := ⟨"y@1", ()⟩
private def y2 : Core.Expression.Ident := ⟨"y@2", ()⟩
private def y3 : Core.Expression.Ident := ⟨"y@3", ()⟩

/-- The assertion of the SSA form. -/
private abbrev growCond : Core.Expression.Expr := .app () (.app () Core.intGtOp (v y3)) (v x0)

/-- The parameter types, parameters and aliases of the procedure. -/
private abbrev tys := growProc.paramTys
private abbrev xs := growProc.entryParams
private abbrev al := growProc.oldAliases

/-- The run of the SSA phase on the body, from no names to avoid. -/
private def growRun := Imperative.WP.ssaEntry ∅ tys xs al growBody

/-- The entry renaming and the output of the run. -/
private def growRen : Imperative.WP.Ren Core.Expression := match growRun with
  | .ok r => r.1
  | .error _ => default
private def growOut : Imperative.WP.SOut Core.Expression := match growRun with
  | .ok r => r.2
  | .error _ => ⟨[], [], [], 0⟩

/-- The metadata of the two definitions of the SSA form: the phase records the source
    metadata with what it did. -/
private def tgtMd : MetaData Core.Expression × MetaData Core.Expression :=
  match growOut.out with
  | [Stmt.cmd (CmdExt.cmd (Cmd.init _ _ _ md1)), Stmt.cmd (CmdExt.cmd (Cmd.init _ _ _ md2)), _] =>
    (md1, md2)
  | _ => default

/-- The SSA form of the body. -/
private abbrev growTgt : Core.Statements :=
  [Core.Statement.init y2 intLTy (.det (addE (v x0) (.intConst () 1))) tgtMd.1] ++
  ([Core.Statement.init y3 intLTy (.det (addE (v y2) (v y2))) tgtMd.2] ++
  [Core.Statement.assert "grow" growCond assertMd])

/-- The SSA phase succeeds on the body. -/
private theorem grow_run : growRun = .ok (growRen, growOut) := by
  have h : (match growRun with | .ok _ => true | .error _ => false) = true := by native_decide
  unfold growRen growOut
  revert h
  generalize growRun = r
  cases r with
  | error => intro h; cases h
  | ok r => intro _; rfl

/-- The SSA phase turns the body into `growTgt`. -/
private theorem grow_ssa : growOut.out = growTgt := by native_decide

/-- The free variables of the body. -/
private theorem grow_freeVars : Block.freeVars growBody = [yId, xId, yId, yId, yId, xId] := by
  native_decide

/-- The entry renaming sends `x` to `x@0`. -/
private theorem ren_x : (_root_.Core.WP.ssaEntryRenOf ∅ tys xs al growBody).get xId = x0 := by
  native_decide
/-- The entry renaming sends `y` to `y@1`. -/
private theorem ren_y : (_root_.Core.WP.ssaEntryRenOf ∅ tys xs al growBody).get yId = y1 := by
  native_decide

/-- The parameters of the procedure are `x` and `y`. -/
private theorem xs_eq : xs = [xId, yId] := by native_decide
/-- The procedure has no `old` aliases. -/
private theorem al_eq : al = [] := by native_decide
/-- The parameter `x` has type `int`. -/
private theorem tys_x : Imperative.WP.Tys.get? tys xId = some intLTy := by native_decide
/-- The parameter `y` has type `int`. -/
private theorem tys_y : Imperative.WP.Tys.get? tys yId = some intLTy := by native_decide

/-! ## The triple of the SSA form -/

/-- `x` holds the integer `k`. -/
private abbrev Holds (x : Core.Expression.Ident) (k : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store x = some (intOf ρ.factory k)

/-- `y@2` is not `x@0`. -/
private theorem y2_ne_x0 : y2 ≠ x0 := by decide
/-- `y@3` is not `x@0`. -/
private theorem y3_ne_x0 : y3 ≠ x0 := by decide
/-- `y@3` is not `y@2`. -/
private theorem y3_ne_y2 : y3 ≠ y2 := by decide

/-- **The assertion of the SSA form holds**, from an entry where `x@0` holds a non-negative
    integer. -/
private theorem growTgt_triple :
    Core.Logic.Hoare.Triple π testParams (fun ρ => Pinned ρ ∧ ∃ a, Holds x0 a ρ ∧ 0 ≤ a)
      growTgt (fun _ => True) := by
  refine Core.Logic.Hoare.seq π testParams
    (Mid := fun ρ => Pinned ρ ∧ ∃ a, Holds x0 a ρ ∧ Holds y2 (a + 1) ρ ∧ 0 ≤ a) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.init π testParams _ _ _ _ _ _
      (fun ρ₀ σ' w ⟨hp, a, hx, ha⟩ hev hinit => ?_)
    rw [Core.eval_intAdd (hp ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int _ hx)
      (Core.eval_intConst _ ρ₀.store 1)] at hev
    cases hev
    cases hinit with
    | init _ hnew hoth => exact ⟨hp, a, (hoth _ y2_ne_x0).trans hx, hnew, ha⟩
  refine Core.Logic.Hoare.seq π testParams
    (Mid := fun ρ => Pinned ρ ∧ ∃ a, Holds x0 a ρ ∧ Holds y3 ((a + 1) + (a + 1)) ρ ∧ 0 ≤ a)
    ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.init π testParams _ _ _ _ _ _
      (fun ρ₀ σ' w ⟨hp, a, hx, hy, ha⟩ hev hinit => ?_)
    rw [Core.eval_intAdd (hp ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int _ hy)
      (Core.eval_fvar_int _ hy)] at hev
    cases hev
    cases hinit with
    | init _ hnew hoth => exact ⟨hp, a, (hoth _ y3_ne_x0).trans hx, hnew, ha⟩
  · refine Core.Logic.Hoare.cmd π testParams _ _ _
      (fun ρ₀ σ' emitted ⟨hp, a, hx, hy, ha⟩ _ hstep => ?_)
    cases hstep with
    | cmd_sem hbase =>
      cases hbase with
      | eval_assert =>
        refine ⟨⟨fun _ _ _ => .inl ⟨hp, ?_⟩, trivial⟩, fun _ => trivial⟩
        rw [Core.eval_intGt (hp ▸ Core.coreFactory_intGt) (Core.eval_fvar_int _ hy)
          (Core.eval_fvar_int _ hx), decide_eq_true (by omega)]
        rfl

/-! ## Back to the original body -/

/-- The entry of the SSA form for the entry `ρ` of the body: `x@0` and `y@1` hold the values of
    `x` and `y`, and nothing else is bound. -/
private def entryEnv (ρ : Env Core.Expression) : Env Core.Expression :=
  { ρ with store := fun z => if z = x0 then ρ.store xId else if z = y1 then ρ.store yId else none }

/-- The entries the triple of the body reads: `x` holds a non-negative integer and `y` an
    integer. -/
private abbrev Entry (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ (∃ a, Holds xId a ρ ∧ 0 ≤ a) ∧ ∃ b, Holds yId b ρ

/-- An integer of the runtime factory has type `int`. -/
private theorem int_valueOfTy (f : Core.Expression.Factory) (k : Int) :
    HasVal.valueOfTy (P := Core.Expression) f (intOf f k) intLTy := ⟨rfl, rfl⟩

/-- The entry of the SSA form is related to the entry of the body by the entry renaming. -/
private theorem entryEnv_rel {ρ : Env Core.Expression} (h : Entry ρ) :
    _root_.Core.WP.SSAEntryRel ∅ tys xs al growBody ρ (entryEnv ρ) := by
  obtain ⟨_, ⟨a, hx, _⟩, b, hy⟩ := h
  have hx0 : (entryEnv ρ).store x0 = ρ.store xId := by simp [entryEnv]
  have hy1 : (entryEnv ρ).store y1 = ρ.store yId := by simp [entryEnv, show y1 ≠ x0 by decide]
  refine ⟨rfl, fun z hz => ?_, fun z hz => ?_, fun z hz _ ty hty w hw => ?_, fun z hz => ?_⟩
  · rw [grow_freeVars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact ⟨by rw [ren_y, hy1], by rw [hy]; rfl⟩
      | exact ⟨by rw [ren_x, hx0], by rw [hx]; rfl⟩
  · rw [xs_eq] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rw [hx]; rfl
    · rw [hy]; rfl
  · rw [grow_freeVars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (rw [tys_y] at hty; cases hty; rw [hy] at hw; cases hw; exact int_valueOfTy _ b)
      | (rw [tys_x] at hty; cases hty; rw [hx] at hw; cases hw; exact int_valueOfTy _ a)
  · simp only [entryEnv] at hz
    split at hz
    · exact ⟨xId, by rw [grow_freeVars]; simp, by rw [ren_x]; assumption⟩
    · split at hz
      · exact ⟨yId, by rw [grow_freeVars]; simp, by rw [ren_y]; assumption⟩
      · simp at hz

/-- **The assertion `grow` holds on every completed run of `Grow`'s body**, from every entry
    where `x` holds a non-negative integer and `y` an integer, from the triple of its SSA form
    (`Core.WP.ssa_triple`). -/
theorem grow_assert_holds :
    Core.Logic.Hoare.Triple π testParams Entry growBody (fun _ => True) :=
  _root_.Core.WP.ssa_triple π testParams (fun _ h => by simp [testParams] at h) ∅ tys xs al
    (by rw [al_eq]; simp) grow_run (by native_decide) (by native_decide)
    (by rw [grow_freeVars, xs_eq]; decide)
    (fun _ h => h.1)
    (fun ρ₀ h _ => ⟨entryEnv ρ₀, entryEnv_rel h, h.1, by
      obtain ⟨a, hx, ha⟩ := h.2.1
      refine ⟨a, ?_, ha⟩
      show (if x0 = x0 then ρ₀.store xId else if x0 = y1 then ρ₀.store yId else none) =
        some (intOf ρ₀.factory a)
      rw [ite_eq_left (rfl : x0 = x0)]
      exact hx⟩)
    (grow_ssa ▸ growTgt_triple)

end Strata.HoareAfterSSATest
