/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.IntEvalProps
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # A contract that rests on integer division and remainder

`Recombine` splits an arbitrary integer `x` into `x div 16` and `x mod 16` and puts it back
together. Its contract `r == x` holds because, in every model, `Int.Div` and `Int.Mod` are `/`
and `%` at a non-zero divisor (`Core.eval_intDiv`, `Core.eval_intMod`), where
`x / 16 * 16 + x % 16 = x`.

Key result: `recombine_meets_contract`.
-/

open StrataDDM (Program)

namespace Strata.HoareIntDivModTest

open Strata.HoareUtils
open Lambda

private def divPgm : Program :=
#strata
program Core;

procedure Recombine(x : int, out r : int)
spec {
  ensures [same]: r == x;
}
{
  r := int.add(int.mul(int.div(x, 16), 16), int.mod(x, 16));
};
#end

private def divAST : Core.Program := typeCheckedAST divPgm

private abbrev xId : Core.Expression.Ident := ⟨"x", ()⟩
private abbrev rId : Core.Expression.Ident := ⟨"r", ()⟩
private abbrev c16 : Core.Expression.Expr := .intConst Core.valueLoc 16

/-- `int.add(int.mul(int.div(x, 16), 16), int.mod(x, 16))`. -/
private abbrev bodyE : Core.Expression.Expr :=
  .app Core.valueLoc
    (.app Core.valueLoc Core.intAddOp
      (.app Core.valueLoc
        (.app Core.valueLoc Core.intMulOp
          (.app Core.valueLoc (.app Core.valueLoc Core.intDivOp (v xId)) c16)) c16))
    (.app Core.valueLoc (.app Core.valueLoc Core.intModOp (v xId)) c16)

/-- `r == x`. -/
private abbrev postE : Core.Expression.Expr := .eq Core.valueLoc (v rId) (v xId)

private def recMd : Imperative.MetaData Core.Expression :=
  match bodyOf divAST "Recombine" with
  | [.cmd (.cmd (.set _ _ md))] => md
  | _ => #[]

/-- `Recombine` consists of the single assignment to `r`. -/
private theorem rec_body_shape :
    (procOf divAST "Recombine").body =
      .structured [Core.Statement.set rId bodyE recMd] false := by
  native_decide

private theorem rec_post_shape :
    ∀ lc ∈ (procOf divAST "Recombine").spec.postconditions.toList, lc.2.expr = postE := by
  native_decide

/-- A built-in of `Core.Factory` resolves the same way in a runtime factory over the
    procedure's factory. -/
private theorem builtin {F : Core.Expression.Factory}
    (hF : F.factory = divAST.factoryBeforeProcedure "Recombine")
    {n : String} {fn : LFunc Core.CoreLParams} (h : Core.Factory[n]? = some fn) :
    F.factory[n]? = some fn :=
  hF ▸ Core.Program.factoryBeforeProcedure_getElem?_of_core divAST "Recombine" h

/-- **`Recombine` meets its contract**: `x div 16 * 16 + x mod 16` is `x`. -/
theorem recombine_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple divAST testParams "Recombine" := by
  let command : Core.Command :=
    Imperative.CmdExt.cmd (Imperative.Cmd.set rId (.det bodyE) recMd)
  refine Core.Logic.Hoare.Procedure.contractTriple_singleton_cmd (hmono := by native_decide)
    (opq := false) divAST testParams "Recombine" (procOf divAST "Recombine") (by native_decide)
    command ?_ (by native_decide) ?_ ?_
  · simpa [command] using rec_body_shape
  · intro ρ₀ σ' emitted hpre hwf hstep
    obtain ⟨-, hfac, -, hin, -⟩ := hpre
    obtain ⟨k, hk⟩ := Core.Logic.Hoare.Procedure.inputAsPredicate_int hwf.storeWellDefined hin
      xId (by native_decide)
    let F := ρ₀.factory
    have hxE := Core.eval_fvar_int (m := Core.valueLoc) (ty := some intMono) F hk
    have h16 := Core.eval_intConst F (m := Core.valueLoc) ρ₀.store 16
    -- The assigned expression evaluates to `k / 16 * 16 + k % 16`.
    have hbody : Core.Expression.eval F ρ₀.store bodyE =
        some (SemValue.ofInt F.model.tcInterp (k / 16 * 16 + k % 16)) :=
      Core.eval_intAdd (builtin hfac Core.coreFactory_intAdd)
        (Core.eval_intMul (builtin hfac Core.coreFactory_intMul)
          (Core.eval_intDiv (builtin hfac Core.coreFactory_intDiv) hxE h16 (by decide)) h16)
        (Core.eval_intMod (builtin hfac Core.coreFactory_intMod) hxE h16 (by decide))
    dsimp [command] at hstep
    cases hstep with
    | cmd_sem hcmd =>
      cases hcmd with
      | eval_set heval hupdate _ _ =>
        have hv := Option.some.inj (heval.symm.trans hbody)
        cases hupdate with
        | update _ hnew hoth =>
          rw [hv, show k / 16 * 16 + k % 16 = k by omega] at hnew
          refine ⟨True.intro, fun _ label check hmem _ _ => .inl ⟨hfac, ?_⟩⟩
          change Core.Expression.eval F σ' check.expr = some (Imperative.HasBool.ttVal F)
          rw [rec_post_shape _ hmem]
          exact Core.eval_eq_true F (Core.eval_fvar_int F hnew)
            (Core.eval_fvar_int F ((hoth xId (by decide)).trans hk))
  · exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [command, Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
        Imperative.Cmd.definedVars])

end Strata.HoareIntDivModTest
