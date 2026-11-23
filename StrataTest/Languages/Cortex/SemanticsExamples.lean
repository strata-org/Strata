/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Cortex.SafeRefsProps
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.Identifiers
import all Strata.Languages.Cortex.Module

/-! # Derivations of the Cortex relation on small programs

Each example derives the expected steps of the relation `StepCortex` for one shape of
program: a caught throw, an exception raised by a callee with `throws` and caught by the
caller, an uncaught exception in a procedure without `throws`, a virtual call with one
overrider, a field write followed by a read, a call of a procedure whose input is also an
output, as `LowerGlobals` writes a procedure that writes a global, and the declaration and
assignment of a variable of the constrained type `int32`. -/

namespace Cortex.Sem.Test

open Imperative

/-- A throw of a safe reference whose class has a covering handler jumps to the handler's
target with the binder set to the exception, emitting no event. -/
example {Γ fr t e md cs tr s v ty} {h : Handler}
    (he : ceval Γ s.env.factory s.env.store e = some v) (hsafe : SafeRef s.env.factory s.heap v)
    (hty : semDynType Γ s.env.factory v = some ty)
    (hh : fr.body.handlerFor? Γ t (tcon ty) = some h) :
    StepCortex Γ (EvalIRCmd Γ) (.inBlock fr t (.throw e md :: cs) tr s) []
      (.atBlock fr h.target ⟨{ s.env with store := s.env.store.update h.binder v }, s.heap⟩) :=
  .cmd_caught (EvalIRCmd.throw he hsafe) hty hh

/-- A callee with `throws`, entered with a store of safe references, that ends with the
exception `v` makes the call raise `v`, and the caller's covering handler catches it after the
callee's events. -/
example {Γ fr t lhs n args md cs tr s p σ₀ evs sE v σG vals σ' ty} {h : Handler}
    (hp : Γ.findProcedure? n = some p)
    (hcf : CallFrame Γ s.env.factory s.env.store p args σ₀)
    (hσ₀ : StoreSafe s.env.factory s.heap σ₀)
    (hrun : RunBody Γ p ⟨⟨σ₀, s.env.factory⟩, s.heap⟩ evs (.raised sE v))
    (hnd : lhs.Nodup)
    (hback : GlobalsBack Γ s.env.factory s.env.store sE.env.store σG)
    (hread : ReadValues s.env.factory sE.env.store ((inoutResults p lhs).map Prod.snd) vals)
    (hvt : List.Rel₂ (HasVal.valueOfStoredTy (P := Core.Expression) s.env.factory σG)
      ((inoutResults p lhs).map Prod.fst) vals)
    (hup : UpdateStates σG ((inoutResults p lhs).map Prod.fst) vals σ')
    (hty : semDynType Γ s.env.factory v = some ty)
    (hh : fr.body.handlerFor? Γ t (tcon ty) = some h) :
    StepCortex Γ (EvalIRCmd Γ) (.inBlock fr t (.call lhs n args md :: cs) tr s)
      (requiresEvents Γ p md s.env.factory σ₀ ++
        checkEvents Γ (entryChecks Γ p) s.env.factory σ₀ ++ evs)
      (.atBlock fr h.target
        ⟨{ s.env with store := σ'.update h.binder v }, sE.heap⟩) :=
  .cmd_caught (EvalIRCmd.call (.raised hp hcf hσ₀ hrun hnd hback hread hvt hup)) hty hh

/-- An uncaught throw of a safe reference in a procedure without `throws` emits one `uncaught`
event and returns normally. -/
example {Γ fr t e md cs tr s v ty}
    (he : ceval Γ s.env.factory s.env.store e = some v) (hsafe : SafeRef s.env.factory s.heap v)
    (hty : semDynType Γ s.env.factory v = some ty)
    (hh : fr.body.handlerFor? Γ t (tcon ty) = none) (hthrows : fr.throws = none) :
    StepCortex Γ (EvalIRCmd Γ) (.inBlock fr t (.throw e md :: cs) tr s)
      [.uncaught s.env.factory s.env.store md "uncaught exception is not thrown"]
      (.returned s) :=
  .cmd_uncaught_nothrows (EvalIRCmd.throw he hsafe) hty hh hthrows

/-- An uncaught exception raised by a call in a procedure without `throws` emits the
call's events, then one `uncaught` event, and returns normally. -/
example {Γ fr t lhs n args md cs tr s s' v evs ty}
    (hc : CallProc Γ s lhs n args md s' (.exn v) evs)
    (hty : semDynType Γ s.env.factory v = some ty)
    (hh : fr.body.handlerFor? Γ t (tcon ty) = none) (hthrows : fr.throws = none) :
    StepCortex Γ (EvalIRCmd Γ) (.inBlock fr t (.call lhs n args md :: cs) tr s)
      (evs ++ [.uncaught s'.env.factory s'.env.store md (raiseSummary Γ (.call lhs n args md))])
      (.returned s') :=
  .cmd_uncaught_nothrows (EvalIRCmd.call hc) hty hh hthrows

/-- A virtual call on a receiver of class `B` runs the method that dispatch selects for
`B`, here its overrider `B$m`. -/
example {Γ lhs r rs md s v s' o evs} (hd : Γ.dispatch "A" "m" (tcon "B") = "B$m")
    (hr : ceval Γ s.env.factory s.env.store r = some v)
    (hty : semDynType Γ s.env.factory v = some "B")
    (hc : CallProc Γ s lhs "B$m" (r :: rs) md s' o evs) :
    EvalIRCmd Γ s (.virtualCall lhs "A" "m" (r :: rs) md) s' o evs :=
  .virtualCall hr hty (hd ▸ hc)

/-- In a lawful heap model, a field write followed by a read of the same field of the
same reference reads the written value. -/
example {Γ s x obj rhs r md₁ md₂ v w d h' σ'} (hm : HeapApiModel Γ s.env.factory)
    (hd : (r, d) ∈ programFields Γ) (hheap : IsOfTy s.env.factory s.heap heapTy)
    (hv : IsOfTy s.env.factory v refTy)
    (hw : EvalIRCmd Γ s (.writeField obj r rhs md₁) ⟨s.env, h'⟩ .normal [])
    (hobj : ceval Γ s.env.factory s.env.store obj = some v)
    (hrhs : ceval Γ s.env.factory s.env.store rhs = some w)
    (hfd : Γ.findField? r = some d)
    (halloc : apiHolds s.env.factory [("$h", h'), ("$o", v)]
      (allocatedT (apiVar "$h") (apiVar "$o")))
    (hx : UpdateState Core.Expression s.env.store x w σ') :
    EvalIRCmd Γ ⟨s.env, h'⟩ (.readField x obj r md₂) ⟨{ s.env with store := σ' }, h'⟩
      .normal [] := by
  cases hw with
  | writeField hobj' _ hrhs' _ hfd' hty hwr =>
    cases hobj.symm.trans hobj'
    cases hrhs.symm.trans hrhs'
    cases hfd.symm.trans hfd'
    exact .readField hobj halloc hfd (hm.readWriteSame r d hd _ _ _ _ hheap hv hty hwr) hx

/-! ## An input that is also an output -/

/-- The name `g`. -/
def gId : Core.Expression.Ident := ⟨"g", ()⟩

/-- The type `int`. -/
def intTy : Core.Expression.Ty := .forAll [] .int

/-- A body that returns at once. -/
def returnBody : Body :=
  ⟨{ entry := "l", blocks := [("l", { cmds := [], transfer := .finish .empty })] }, []⟩

/-- `bump(g) returns (g)`, the shape `LowerGlobals` gives a procedure that writes the
global `g`: `g` is both its input and its output. -/
def bump : Procedure :=
  { name := "bump", inputs := [(gId, intTy)], outputs := [(gId, intTy)], throws := none,
    body := some returnBody }

/-- A program with `bump` and no globals. -/
def bumpCtx : UnorderedProgram := { composites := [], procedures := [bump] }

/-- `bump`'s only output is also an input, so a call chooses no output value. -/
theorem bump_chosenOutputs : chosenOutputs bump = [] := (rfl)

/-- `int` reads as itself in `bumpCtx`. -/
theorem bump_erase : eraseTy bumpCtx intTy = intTy := by
  simp [eraseTy, eraseMono, constrainedValueTy, constrainedBase, bumpCtx, eraseRefs,
    eraseRefsList, isRefName, intTy, UnorderedProgram.findComposite?, Lambda.LMonoTy.int]

/-- The callee's entry store of a call of `bump` with an integer argument binds `g` to the
argument: the output `g` is also an input, so it gets no value of its own. -/
theorem bump_callFrame {f σ args v}
    (hargs : EvalExpressions f σ (args.map (eraseExpr bumpCtx)) [v]) (hv : IsOfTy f v .int) :
    CallFrame bumpCtx f σ bump args (emptyStore.update gId v) := by
  refine ⟨[], [v], [], emptyStore, emptyStore.update gId v, .read_none, .init_none, hargs,
    .cons (by dsimp only; rw [bump_erase]; exact hv) .nil, .init_some (.init rfl ?_ fun y hy => ?_) .init_none, ?_, ?_⟩
  · simp [SemanticStore.update]
  · simp [SemanticStore.update, Ne.symm hy]
  · rw [bump_chosenOutputs]; exact .nil
  · rw [bump_chosenOutputs]; exact .init_none

/-- A call `g := bump(…)` whose argument is an integer and a safe reference, with `g` holding
an integer, returns normally, with no event, and writes the callee's final `g`, the argument,
back to the caller's `g`. -/
example {s args v w} (hargs : EvalExpressions s.env.factory s.env.store
      (args.map (eraseExpr bumpCtx)) [v]) (hv : IsOfTy s.env.factory v .int)
    (hsafe : SafeRef s.env.factory s.heap v)
    (hw : s.env.store gId = some w) (hwt : IsOfTy s.env.factory w .int) :
    CallProc bumpCtx s [gId] "bump" args .empty
      ⟨{ s.env with store := s.env.store.update gId v }, s.heap⟩ .normal [] := by
  have hcmds : ∀ σ₀ : Store, (procFrame bumpCtx bump returnBody σ₀).blockCmds bumpCtx
      { cmds := [], transfer := .finish .empty } = [] := fun _ => (rfl)
  have hrun : RunBody bumpCtx bump ⟨⟨emptyStore.update gId v, s.env.factory⟩, s.heap⟩ []
      (.returned ⟨⟨emptyStore.update gId v, s.env.factory⟩, s.heap⟩) := by
    refine .returned rfl (.step _ [] _ [] _ (.fetch rfl) ?_)
    rw [hcmds]
    exact .step _ [] _ [] _ .finish (.refl _)
  have hup : UpdateStates s.env.store [gId] [v] (s.env.store.update gId v) :=
    .update_some (.update hw (by simp [SemanticStore.update]) fun y hy => by
      simp [SemanticStore.update, Ne.symm hy]) .update_none
  exact .normal (sE := ⟨⟨emptyStore.update gId v, s.env.factory⟩, s.heap⟩) rfl
    (bump_callFrame hargs hv) (storeSafe_empty.update hsafe) hrun (by simp)
    (.read_some (by simp [SemanticStore.update]) hv.1 .read_none) (.cons ⟨w, _, hw, hwt, hv⟩ .nil)
    hup ⟨[], .read_none, .update_none⟩

/-! ## A variable of a constrained type -/

/-- The type `int32`. -/
def int32Ty : Core.Expression.Ty := .forAll [] (.tcons "int32" [])

/-- A program declaring `int32`, a constrained type over `int`, as the Java front end
declares it. -/
def int32Ctx : UnorderedProgram :=
  { composites := [], procedures := [],
    constrained := [{ name := "int32", base := intTy, binder := ⟨"x", ()⟩,
                      constraint := .boolConst Core.coreLoc true }] }

/-- The name `i`. -/
def iId : Core.Expression.Ident := ⟨"i", ()⟩

/-- `int32` reads as its base type `int`. -/
theorem int32_erase : eraseTy int32Ctx int32Ty = intTy := by
  simp [int32Ty, eraseTy, eraseMono, constrainedValueTy, int32Ctx, constrainedBase, eraseRefs,
    eraseRefsList, isRefName, intTy, UnorderedProgram.findComposite?, Lambda.LMonoTy.int]

/-- `init i : int32 := 0` steps: the value `0` of sort `int` is a value of `int32`'s base
type. -/
example {s σ' md} (hvar : WellFormedSemanticEvalVar (P := Core.Expression) s.env.factory)
    (hσ : InitState Core.Expression s.env.store iId
      (Lambda.SemValue.ofInt s.env.factory.model.tcInterp 0) σ') :
    EvalIRCmd int32Ctx s (.cmd (.init iId int32Ty (.det (.intConst Core.coreLoc 0)) md))
      ⟨{ s.env with store := σ' }, s.heap⟩ .normal [] := by
  refine .base (evs := []) ?_ (safe_writes_initState hσ (safeRef_of_isOfTy (t := .int) ⟨rfl, rfl⟩
    (by decide)))
  exact .eval_init Lambda.LExpr.denoteEval_intConst hσ ⟨rfl, by rw [int32_erase]; rfl⟩ hvar

/-- `i := 1` steps on a variable `i` that holds an `int`. -/
example {s σ' md} (hvar : WellFormedSemanticEvalVar (P := Core.Expression) s.env.factory)
    (hi : s.env.store iId = some (Lambda.SemValue.ofInt s.env.factory.model.tcInterp 0))
    (hσ : UpdateState Core.Expression s.env.store iId
      (Lambda.SemValue.ofInt s.env.factory.model.tcInterp 1) σ') :
    EvalIRCmd int32Ctx s (.cmd (.set iId (.det (.intConst Core.coreLoc 1)) md))
      ⟨{ s.env with store := σ' }, s.heap⟩ .normal [] := by
  refine .base (evs := []) ?_ (safe_writes_updateState hσ
    (safeRef_of_isOfTy (t := .int) ⟨rfl, rfl⟩ (by decide)))
  exact .eval_set Lambda.LExpr.denoteEval_intConst hσ ⟨_, intTy, hi, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ hvar

/-- The block `init i : int32 := 0` runs its declaration followed by the check of the
constraint of `int32` on `i`. -/
example {fr : Fr} {md} (hv : fr.vars = [("i", "int32")]) :
    fr.blockCmds int32Ctx
        { cmds := [.cmd (.init iId int32Ty (.det (.intConst Core.coreLoc 0)) md)],
          transfer := .condGoto (.boolConst Core.coreLoc true) "a" "b" .empty } =
      .cmd (.init iId int32Ty (.det (.intConst Core.coreLoc 0)) md) ::
        (checkOf int32Ctx true "int32" (mkFvar "i") md).map .cmd := by
  simp [Fr.blockCmds, checkedCmd, checkedBaseCmd, checkVar, hv, iId]

end Cortex.Sem.Test
