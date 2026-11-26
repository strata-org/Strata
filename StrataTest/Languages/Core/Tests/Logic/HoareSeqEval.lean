/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.SeqEvalProps
import Strata.Languages.Core.BoolEvalProps
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # A contract over a sequence the procedure does not build

`ReadAt` reads `s` at `i` with the total `Sequence.select!` and ensures the result is
`Sequence.select(s, i)`. Its input sequence is arbitrary, so the concrete evaluator cannot run
the body; the proof instead evaluates the precondition and the postcondition with the
evaluation lemmas of `Strata.Languages.Core.SeqEvalProps` and `BoolEvalProps`, and closes the
postcondition with `Core.seqSelectBang_eq_select`: in every model, the two selectors agree in
range, which is what the precondition gives. The program declares a function before the
procedure, so the procedure's factory is not `Core.Factory`; it still resolves the built-ins
(`Core.Program.factoryBeforeProcedure_getElem?_of_core`).

Key result: `readAt_meets_contract`.
-/

open StrataDDM (Program)

namespace Strata.HoareSeqEvalTest

open Strata.HoareUtils
open Lambda

private def seqPgm : Program :=
#strata
program Core;

function twice(x : int) : int { int.mul(x, 2) }

procedure ReadAt(s : Sequence int, i : int, out r : int)
spec {
  requires [inRange]: int.le(0, i) && int.lt(i, Sequence.length(s));
  ensures [same]: r == Sequence.select(s, i);
}
{
  r := Sequence.select!(s, i);
};
#end

private def seqAST : Core.Program := typeCheckedAST seqPgm

private abbrev seqInt : LMonoTy := .tcons "Sequence" [intMono]
private abbrev sId : Core.Expression.Ident := ⟨"s", ()⟩
private abbrev iId : Core.Expression.Ident := ⟨"i", ()⟩
private abbrev rId : Core.Expression.Ident := ⟨"r", ()⟩
private abbrev sV : Core.Expression.Expr := .fvar Core.valueLoc sId (some seqInt)

/-- `Sequence.length(s)`. -/
private abbrev lenE : Core.Expression.Expr :=
  .app Core.valueLoc
    (.op Core.valueLoc ⟨"Sequence.length", ()⟩ (some (.arrow seqInt intMono))) sV

/-- `name(s, i)`, for a selector `name` at `Sequence int → int → int`. -/
private abbrev selE (name : String) : Core.Expression.Expr :=
  .app Core.valueLoc
    (.app Core.valueLoc
      (.op Core.valueLoc ⟨name, ()⟩ (some (.arrow seqInt (.arrow intMono intMono)))) sV)
    (v iId)

/-- `int.le(0, i) && int.lt(i, Sequence.length(s))`. -/
private abbrev preE : Core.Expression.Expr :=
  .app Core.valueLoc
    (.app Core.valueLoc Core.boolAndOp
      (.app Core.valueLoc (.app Core.valueLoc Core.intLeOp (.intConst Core.valueLoc 0)) (v iId)))
    (.app Core.valueLoc (.app Core.valueLoc Core.intLtOp (v iId)) lenE)

/-- `r == Sequence.select(s, i)`. -/
private abbrev postE : Core.Expression.Expr := .eq Core.valueLoc (v rId) (selE "Sequence.select")

private def readMd : Imperative.MetaData Core.Expression :=
  match bodyOf seqAST "ReadAt" with
  | [.cmd (.cmd (.set _ _ md))] => md
  | _ => #[]

/-- `ReadAt` consists of the single assignment `r := Sequence.select!(s, i)`. -/
private theorem read_body_shape :
    (procOf seqAST "ReadAt").body =
      .structured [Core.Statement.set rId (selE "Sequence.select!") readMd] false := by
  native_decide

private theorem read_pre_shape :
    ∀ lc ∈ (procOf seqAST "ReadAt").spec.preconditions.toList, lc.2.expr = preE := by
  native_decide

private theorem read_post_shape :
    ∀ lc ∈ (procOf seqAST "ReadAt").spec.postconditions.toList, lc.2.expr = postE := by
  native_decide

private theorem read_pre_ne : (procOf seqAST "ReadAt").spec.preconditions.toList ≠ [] := by
  native_decide

/-- The factory visible to `ReadAt`: Core's built-ins and the function `twice`. -/
private abbrev readFactory : Lambda.Factory Core.CoreLParams :=
  seqAST.factoryBeforeProcedure "ReadAt"

/-- A built-in of `Core.Factory` resolves the same way in a runtime factory over
    `readFactory`, although the program declares a function before the procedure. -/
private theorem builtin {F : Core.Expression.Factory} (hF : F.factory = readFactory)
    {n : String} {fn : LFunc Core.CoreLParams} (h : Core.Factory[n]? = some fn) :
    F.factory[n]? = some fn :=
  hF ▸ Core.Program.factoryBeforeProcedure_getElem?_of_core seqAST "ReadAt" h

/-- An input of type `Sequence int` holds a sequence of the runtime factory. -/
private theorem seq_input {ρ : Imperative.Env Core.Expression}
    (hwf : Imperative.WellFormedStore ρ.store ρ.factory)
    (hin : Core.Logic.Hoare.Procedure.inputAsPredicate (procOf seqAST "ReadAt") ρ) :
    ∃ sv : SortDenote ρ.factory.model.tcInterp (.tcons "Sequence" [.int]),
      ρ.store sId = some ⟨ρ.factory.model.tcInterp, .tcons "Sequence" [.int], sv⟩ := by
  obtain ⟨w, hw, hty⟩ := hin sId seqInt (by native_decide)
  have htc := hwf sId w hw
  obtain ⟨tc, srt, val⟩ := w
  obtain rfl : srt = .tcons "Sequence" [.int] := LSort.toMonoTy_injective (t := .tcons "Sequence" [.int]) hty
  obtain rfl : tc = ρ.factory.model.tcInterp := htc
  exact ⟨val, hw⟩

/-- **`ReadAt` meets its contract**: in range, `select!` reads what `select` does. -/
theorem readAt_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "ReadAt" := by
  let command : Core.Command :=
    Imperative.CmdExt.cmd (Imperative.Cmd.set rId (.det (selE "Sequence.select!")) readMd)
  refine Core.Logic.Hoare.Procedure.contractTriple_singleton_cmd (hmono := by native_decide)
    (opq := false) seqAST testParams "ReadAt" (procOf seqAST "ReadAt") (by native_decide)
    command ?_ (by native_decide) ?_ ?_
  · simpa [command] using read_body_shape
  · intro ρ₀ σ' emitted hpre hwf hstep
    obtain ⟨hreq, hfac, -, hin, -⟩ := hpre
    have hsw := hwf.storeWellDefined
    obtain ⟨k, hk⟩ :=
      Core.Logic.Hoare.Procedure.inputAsPredicate_int hsw hin iId (by native_decide)
    obtain ⟨sv, hs⟩ := seq_input hsw hin
    let F := ρ₀.factory
    have hsE : Core.Expression.eval F ρ₀.store sV = some ⟨F.model.tcInterp, _, sv⟩ :=
      Core.eval_fvar (m := Core.valueLoc) (ty := some seqInt) F hs rfl
    have hiE := Core.eval_fvar_int (m := Core.valueLoc) (ty := some intMono) F hk
    -- The precondition: `0 ≤ k` and `k < length(s)`.
    have hlenE := Core.eval_seqLength (m := Core.valueLoc) (m' := Core.valueLoc) (a := intMono)
      rfl hsE
    have hpreE : Core.Expression.eval F ρ₀.store preE =
        some (SemValue.ofBool F.model.tcInterp
          (decide (0 ≤ k) && decide (k < Core.seqLengthOf F.model .int sv))) :=
      Core.eval_boolAnd (builtin hfac Core.coreFactory_boolAnd)
        (Core.eval_intLe (builtin hfac Core.coreFactory_intLe) (Core.eval_intConst F _ 0) hiE)
        (Core.eval_intLt (builtin hfac Core.coreFactory_intLt) hiE hlenE)
    obtain ⟨⟨l, c⟩, hmem⟩ := List.exists_mem_of_ne_nil _ read_pre_ne
    have hrange : 0 ≤ k ∧ k < Core.seqLengthOf F.model .int sv := by
      rcases hreq l c hmem ⟨fun _ => False⟩ with ⟨_, he⟩ | ⟨hnf, _⟩
      · change Core.Expression.eval F ρ₀.store c.expr =
          some (Imperative.HasBool.ttVal F) at he
        rw [read_pre_shape _ hmem, hpreE] at he
        have := SemValue.ofBool_injective (Option.some.inj he)
        simpa using this
      · exact absurd hfac hnf
    -- The step: `r` takes the value `select!(s, k)`.
    dsimp [command] at hstep
    cases hstep with
    | cmd_sem hcmd =>
      cases hcmd with
      | eval_set heval hupdate _ _ =>
        have hbang := Core.eval_seqSelectBang (m := Core.valueLoc) (m' := Core.valueLoc)
          (m'' := Core.valueLoc) (a := intMono) rfl hsE hiE
        have hv := Option.some.inj (heval.symm.trans hbang)
        cases hupdate with
        | update _ hnew hoth =>
          rw [hv] at hnew
          refine ⟨True.intro, fun _ label check hmem' _ _ => .inl ⟨hfac, ?_⟩⟩
          change Core.Expression.eval F σ' check.expr = some (Imperative.HasBool.ttVal F)
          rw [read_post_shape _ hmem']
          -- In `σ'`, `s` and `i` are unchanged and `r` holds `select!(s, k)`, which is
          -- `select(s, k)` in range.
          have hs' : σ' sId = some ⟨F.model.tcInterp, _, sv⟩ := (hoth sId (by decide)).trans hs
          have hk' : σ' iId = some (SemValue.ofInt F.model.tcInterp k) :=
            (hoth iId (by decide)).trans hk
          have hsel := Core.eval_seqSelect (m := Core.valueLoc) (m' := Core.valueLoc)
            (m'' := Core.valueLoc) (a := intMono) rfl
            (Core.eval_fvar (m := Core.valueLoc) (ty := some seqInt) F hs' rfl)
            (Core.eval_fvar_int (m := Core.valueLoc) (ty := some intMono) F hk')
          have hagree := Core.seqSelectBang_eq_select F.model
            (builtin hfac Core.coreFactory_seqSelect) (builtin hfac Core.coreFactory_boolAnd)
            (builtin hfac Core.coreFactory_intLe) (builtin hfac Core.coreFactory_intLt)
            (intMono.substTyVars F.tyVarVal) sv k hrange.1 hrange.2
          refine Core.eval_eq_true F (Core.eval_fvar F hnew rfl) ?_
          rw [hagree]
          exact hsel
  · exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [command, Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
        Imperative.Cmd.definedVars])

end Strata.HoareSeqEvalTest
