/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import Strata.Languages.Core.IntEvalProps

import Strata.Languages.Core
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.Logic.HoareCall
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Imperative.Logic.HoareTemplate
import Strata.DL.Lambda.OperationalSemantics
import StrataDDM.Integration.Lean.HashCommands
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core

/-! # A procedure contract for an unstructured (CFG) sum-to-n loop

`sumToNPgm` is `sum_to_n` written as a control-flow graph: the loop is a backward
`goto` from `body` to `loop`.  The final result is
`Core.Logic.Hoare.Procedure.contractTriple sumToNAST testParams "sum_to_n"`, read over
`EventLang.coreCFG` from the entry block to a terminal configuration.
-/

open Imperative
open StrataDDM (Program)
open Lambda.LExpr.SyntaxMono

private def sumToNPgm : Program :=
#strata
program Core;

// sum_to_n as an unstructured CFG: the loop is a backward goto from `body` to `loop`.
procedure sum_to_n(n : int, out result : int)
spec {
  requires (int.ge(n, 0));
  ensures ((int.mul(2, result) == int.mul(n, int.add(n, 1))));
}
cfg entry {
  entry: {
    var i : int;
    var s : int;
    i := 0;
    s := 0;
    goto loop;
  }
  loop: {
    branch (int.lt(i, n)) goto body else goto done;
  }
  body: {
    i := int.add(i, 1);
    s := int.add(s, i);
    goto loop;
  }
  done: {
    result := s;
    return;
  }
};
#end


namespace Strata

open CoreHoareTestSupport

private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def sumToNAST := cstToAST sumToNPgm
private def sumToNProc : Core.Procedure := (sumToNAST.findProcByString? "sum_to_n").get!
private def sumToNCFG : Core.DetCFG := match sumToNProc.body with | .cfg cfg => cfg | _ => default

/-! ## Identifiers and expression shapes -/

private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def iId : Core.Expression.Ident := ⟨"i", ()⟩
private def sId : Core.Expression.Ident := ⟨"s", ()⟩
private def resultId : Core.Expression.Ident := ⟨"result", ()⟩

private def intTy : Option Lambda.LMonoTy := some .int
private def intLTy : Lambda.LTy := .forAll [] .int
private def iExpr : Core.Expression.Expr := .fvar () iId intTy
private def sExpr : Core.Expression.Expr := .fvar () sId intTy
private def nExpr : Core.Expression.Expr := .fvar () nId intTy
private def resultExpr : Core.Expression.Expr := .fvar () resultId intTy
private def zeroExpr : Core.Expression.Expr := .const () (.intConst 0)
private def oneExpr : Core.Expression.Expr := .const () (.intConst 1)
private def trueExpr : Core.Expression.Expr := .const () (.boolConst true)
/-- `int.lt(i, n)` -/
private def ltExpr : Core.Expression.Expr :=
  .app () (.app () (Lambda.intLtFunc (T := Core.CoreLParams)).opExpr iExpr) nExpr
/-- `int.add(i, 1)` -/
private def incExpr : Core.Expression.Expr := .app () (.app () Core.coreIntAddOpExpr iExpr) oneExpr
/-- `int.add(s, i)` -/
private def addExpr : Core.Expression.Expr :=
  .app () (.app () (Lambda.intAddFunc (T := Core.CoreLParams)).opExpr sExpr) iExpr

/-! ## The translated CFG, spelled out -/

/-- Metadata of the `k`-th command of block `l` of `cfg`. -/
private def cmdMdOf (cfg : Core.DetCFG) (l : String) (k : Nat) : MetaData Core.Expression :=
  match cfg.blocks.lookup l with
  | some b =>
    match b.cmds[k]? with
    | some (.cmd (.init _ _ _ md)) => md
    | some (.cmd (.set _ _ md)) => md
    | _ => #[]
  | none => #[]

/-- Metadata of the transfer of block `l` of `cfg`. -/
private def transferMdOf (cfg : Core.DetCFG) (l : String) : MetaData Core.Expression :=
  match cfg.blocks.lookup l with
  | some { transfer := .condGoto _ _ _ md, .. } => md
  | some { transfer := .finish md, .. } => md
  | _ => #[]

/-- Metadata of the `k`-th command of block `l` in the translated SumToN CFG. -/
private def cmdMd (l : String) (k : Nat) : MetaData Core.Expression :=
  cmdMdOf sumToNCFG l k
/-- Metadata of the transfer of block `l` in the translated SumToN CFG. -/
private def transferMd (l : String) : MetaData Core.Expression :=
  transferMdOf sumToNCFG l

private def initI : Core.Command := .cmd (.init iId intLTy .nondet (cmdMd "entry" 0))
private def initS : Core.Command := .cmd (.init sId intLTy .nondet (cmdMd "entry" 1))
private def setI0 : Core.Command := .cmd (.set iId (.det zeroExpr) (cmdMd "entry" 2))
private def setS0 : Core.Command := .cmd (.set sId (.det zeroExpr) (cmdMd "entry" 3))
private def setIInc : Core.Command := .cmd (.set iId (.det incExpr) (cmdMd "body" 0))
private def setSAdd : Core.Command := .cmd (.set sId (.det addExpr) (cmdMd "body" 1))
private def setResult : Core.Command := .cmd (.set resultId (.det sExpr) (cmdMd "done" 0))
private def entryMd : MetaData Core.Expression := transferMd "entry"
private def loopMd : MetaData Core.Expression := transferMd "loop"
private def bodyMd : MetaData Core.Expression := transferMd "body"
private def doneMd : MetaData Core.Expression := transferMd "done"

private def expectedCFG : Core.DetCFG :=
  { entry := "entry"
    blocks :=
      [("entry", { cmds := [initI, initS, setI0, setS0],
                   transfer := .condGoto trueExpr "loop" "loop" entryMd }),
       ("loop", { cmds := [], transfer := .condGoto ltExpr "body" "done" loopMd }),
       ("body", { cmds := [setIInc, setSAdd], transfer := .condGoto trueExpr "loop" "loop" bodyMd }),
       ("done", { cmds := [setResult], transfer := .finish doneMd })] }

/-- The translated `sum_to_n` CFG equals the hand-written `expectedCFG`. -/
private theorem sumToN_cfg_eq : sumToNCFG = expectedCFG := by native_decide

/-- Looking up `"entry"` in `expectedCFG` yields its four init/assignment commands
    and the unconditional `goto loop`. -/
private theorem entry_lookup : expectedCFG.blocks.lookup "entry" =
    some { cmds := [initI, initS, setI0, setS0],
           transfer := .condGoto trueExpr "loop" "loop" entryMd } := by native_decide
/-- Looking up `"loop"` in `expectedCFG` yields an empty block whose transfer branches
    on `int.lt(i, n)` to `body` or `done`. -/
private theorem loop_lookup : expectedCFG.blocks.lookup "loop" =
    some { cmds := [], transfer := .condGoto ltExpr "body" "done" loopMd } := by native_decide
/-- Looking up `"body"` in `expectedCFG` yields its two assignments and the backward
    `goto loop`. -/
private theorem body_lookup : expectedCFG.blocks.lookup "body" =
    some { cmds := [setIInc, setSAdd],
           transfer := .condGoto trueExpr "loop" "loop" bodyMd } := by native_decide
/-- Looking up `"done"` in `expectedCFG` yields the `result := s` assignment and the
    `finish` transfer. -/
private theorem done_lookup : expectedCFG.blocks.lookup "done" =
    some { cmds := [setResult], transfer := .finish doneMd } := by native_decide

/-! ## Expression evaluation on a runtime factory over `Core.Factory` -/

/-- The integer `k` as a value of the runtime factory `F`. -/
private abbrev intV (F : Core.Expression.Factory) (k : Int) : Core.Expression.Val :=
  Lambda.SemValue.ofInt F.model.tcInterp k

/-- A free variable that evaluates reads its store binding. -/
private theorem eval_fvar_inv {F : Core.Expression.Factory} {σ : SemanticStore Core.Expression}
    {x : Core.Expression.Ident} {ty : Option Lambda.LMonoTy} {v w : Core.Expression.Val}
    (hx : σ x = some w) (h : Core.Expression.eval F σ (.fvar () x ty) = some v) : v = w := by
  obtain ⟨w', hw', htc⟩ := Lambda.LExpr.denoteEval_defines h x
    (by simp [Lambda.LExpr.LExpr.getVars])
  rw [hx] at hw'
  cases hw'
  exact Option.some.inj (h.symm.trans (Core.eval_fvar F hx htc))

/-- `int.lt(i, n)` with `i ↦ a`, `n ↦ b` evaluates to `a < b`. -/
private theorem eval_lt (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : SemanticStore Core.Expression) (a b : Int)
    (hi : σ iId = some (intV F a)) (hn : σ nId = some (intV F b)) :
    Core.Expression.eval F σ ltExpr
      = some (Lambda.SemValue.ofBool F.model.tcInterp (decide (a < b))) :=
  Core.eval_intLt (hF ▸ Core.coreFactory_intLt) (Core.eval_fvar_int F hi)
    (Core.eval_fvar_int F hn)

/-- `int.add(s, i)` with `s ↦ a`, `i ↦ b` evaluates to `a + b`. -/
private theorem eval_add (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : SemanticStore Core.Expression) (a b : Int)
    (hs : σ sId = some (intV F a)) (hi : σ iId = some (intV F b)) :
    Core.Expression.eval F σ addExpr = some (intV F (a + b)) :=
  Core.eval_intAdd (hF ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int F hs)
    (Core.eval_fvar_int F hi)

/-- `int.add(i, 1)` with `i ↦ a` evaluates to `a + 1`. -/
private theorem eval_inc (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : SemanticStore Core.Expression) (a : Int) (hi : σ iId = some (intV F a)) :
    Core.Expression.eval F σ incExpr = some (intV F (a + 1)) :=
  Core.eval_intAdd (hF ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int F hi)
    (Core.eval_const F σ (.intConst 1))

/-! ## The configuration invariant

The store facts are about integers of a fixed type-constructor interpretation `tc`, the
model's in the runtime factory of the run. -/

/-- `n` is in the store. -/
private def EntryInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  σ nId = some (Lambda.SemValue.ofInt tc nv)
/-- `n` is in the store and `i = 0`. -/
private def HalfInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  σ nId = some (Lambda.SemValue.ofInt tc nv) ∧ σ iId = some (Lambda.SemValue.ofInt tc 0)
/-- The loop invariant: `2 * s = i * (i + 1)` and `i ≤ n`. -/
private def LoopInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  ∃ iv sv : Int, σ nId = some (Lambda.SemValue.ofInt tc nv) ∧
    σ iId = some (Lambda.SemValue.ofInt tc iv) ∧
    σ sId = some (Lambda.SemValue.ofInt tc sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv ≤ nv
/-- Entering the body: the loop invariant and `i < n`. -/
private def BodyInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  ∃ iv sv : Int, σ nId = some (Lambda.SemValue.ofInt tc nv) ∧
    σ iId = some (Lambda.SemValue.ofInt tc iv) ∧
    σ sId = some (Lambda.SemValue.ofInt tc sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv < nv
/-- Between the two body assignments: `i` has been incremented, `s` not yet. -/
private def MidInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  ∃ iv sv : Int, σ nId = some (Lambda.SemValue.ofInt tc nv) ∧
    σ iId = some (Lambda.SemValue.ofInt tc iv) ∧
    σ sId = some (Lambda.SemValue.ofInt tc sv) ∧ 2 * sv = (iv - 1) * iv ∧ iv ≤ nv
/-- Loop exit: the loop invariant and `i = n`. -/
private def DoneInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  ∃ iv sv : Int, σ nId = some (Lambda.SemValue.ofInt tc nv) ∧
    σ iId = some (Lambda.SemValue.ofInt tc iv) ∧
    σ sId = some (Lambda.SemValue.ofInt tc sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv = nv
/-- After `result := s`. -/
private def PostInv (tc : Lambda.TyConstrInterp) (nv : Int) (σ : SemanticStore Core.Expression) :
    Prop :=
  ∃ rv : Int, σ nId = some (Lambda.SemValue.ofInt tc nv) ∧
    σ resultId = some (Lambda.SemValue.ofInt tc rv) ∧ 2 * rv = nv * (nv + 1)

/-- Every configuration reachable from `atBlock "entry"`, with the store facts that hold
    there.  Non-terminal configurations pin the active CFG to `expectedCFG`, and every
    configuration pins the runtime factory to `F`.  Each constructor names one program point of the
    `sum_to_n` CFG run. -/
private inductive RunInv (F : Core.Expression.Factory) (nv : Int) :
    CFGConfig String Core.Command Core.Expression → Prop where
  /-- `atBlock "entry"` (about to fetch the entry block). -/
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : EntryInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.atBlock expectedCFG "entry" ρ)
  /-- `inBlock "entry"` before any entry command has run. -/
  | entryPreInitI (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : EntryInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "entry" [initI, initS, setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after `var i`, before `var s`. -/
  | entryPreInitS (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : EntryInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "entry" [initS, setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after both `var` declarations, before `i := 0`. -/
  | entryPreSetI0 (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : EntryInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "entry" [setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after `i := 0`, before `s := 0` (here `HalfInv` additionally
      records `i = 0`). -/
  | entryPreSetS0 (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : HalfInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "entry" [setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after both assignments, at the `goto loop` transfer (the loop
      invariant now holds). -/
  | entryAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : LoopInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "entry" []
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `atBlock "loop"` (about to fetch the loop header). -/
  | atLoop (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : LoopInv F.model.tcInterp nv ρ.store)
      :
      RunInv F nv (.atBlock expectedCFG "loop" ρ)
  /-- `inBlock "loop"` at the `branch (int.lt(i, n))` transfer. -/
  | loopAtBranch (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : LoopInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "loop" []
        (.condGoto ltExpr "body" "done" loopMd) ρ)
  /-- `atBlock "body"` on the loop-taken branch (`i < n`). -/
  | atBody (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : BodyInv F.model.tcInterp nv ρ.store)
      :
      RunInv F nv (.atBlock expectedCFG "body" ρ)
  /-- `inBlock "body"` before `i := int.add(i, 1)`. -/
  | bodyPreInc (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : BodyInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "body" [setIInc, setSAdd]
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `inBlock "body"` after `i` is incremented, before `s := int.add(s, i)`
      (`MidInv`: `s` not yet updated). -/
  | bodyPreAdd (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : MidInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "body" [setSAdd]
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `inBlock "body"` at the backward `goto loop` transfer (the loop invariant is
      re-established). -/
  | bodyAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : LoopInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "body" []
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `atBlock "done"` on the loop-exit branch (`i = n`). -/
  | atDone (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : DoneInv F.model.tcInterp nv ρ.store)
      :
      RunInv F nv (.atBlock expectedCFG "done" ρ)
  /-- `inBlock "done"` before `result := s`. -/
  | donePreSet (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : DoneInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "done" [setResult] (.finish doneMd) ρ)
  /-- `inBlock "done"` after `result := s`, at the `finish` transfer (`PostInv` now
      holds). -/
  | doneAtFinish (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : PostInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.inBlock expectedCFG "done" [] (.finish doneMd) ρ)
  /-- The `terminal` configuration (`PostInv` on the final store). -/
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : PostInv F.model.tcInterp nv ρ.store) :
      RunInv F nv (.terminal ρ)


/-- A terminal configuration satisfying `RunInv` carries the factory fact and `PostInv`. -/
private theorem runInv_terminal {F : Core.Expression.Factory} {nv : Int} {ρ : Env Core.Expression}
    (h : RunInv F nv (.terminal ρ)) : ρ.factory = F ∧ PostInv F.model.tcInterp nv ρ.store := by
  cases h with
  | terminal _ hf hp => exact ⟨hf, hp⟩

/-! ## One step preserves the invariant -/

/-- Inversion of a `set x := e` command step. -/
private theorem set_inv {π : String → Option Core.Procedure} {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {e : Core.Expression.Expr} {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.set x (.det e) md)) σ' emitted) :
    ∃ v, Core.Expression.eval fac σ e = some v ∧ σ' x = some v ∧
      (∀ y, x ≠ y → σ' y = σ y) ∧ emitted = [] := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_set heval hupdate _ _ =>
    cases hupdate with
    | update _ hres hother => exact ⟨_, heval, hres, hother, rfl⟩

/-- A `set x := e` command step can only fire when `x` is already bound: the
    `UpdateState` it performs requires a prior binding. -/
private theorem set_pre {π : String → Option Core.Procedure} {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {e : Core.Expression.Expr} {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.set x (.det e) md)) σ' emitted) :
    (σ x).isSome = true := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_set heval hupdate _ _ =>
    cases hupdate with
    | update hpre _ _ => simp [hpre]

/-- Inversion of a nondeterministic `init x` command step. -/
private theorem init_inv {π : String → Option Core.Procedure} {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {ty : Lambda.LTy} {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.init x ty .nondet md)) σ' emitted) :
    (∀ y, x ≠ y → σ' y = σ y) ∧ emitted = [] := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ hother => exact ⟨hother, rfl⟩

/-- Two Core identifiers with distinct names are distinct. -/
private theorem ident_ne {a b : String} (h : a ≠ b) :
    (⟨a, ()⟩ : Core.Expression.Ident) ≠ ⟨b, ()⟩ := by
  intro heq
  injection heq with h1
  exact h h1
/-- The identifiers `i` and `n` are distinct. -/
private theorem i_ne_n : iId ≠ nId := ident_ne (by decide)
/-- The identifiers `i` and `s` are distinct. -/
private theorem i_ne_s : iId ≠ sId := ident_ne (by decide)
/-- The identifiers `s` and `n` are distinct. -/
private theorem s_ne_n : sId ≠ nId := ident_ne (by decide)
/-- The identifiers `s` and `i` are distinct. -/
private theorem s_ne_i : sId ≠ iId := ident_ne (by decide)
/-- The identifiers `result` and `n` are distinct. -/
private theorem result_ne_n : resultId ≠ nId := ident_ne (by decide)

/-- One `StepCFGE` step from an invariant-satisfying configuration stays within
    `RunInv` and emits no events. -/
private theorem step_preserves {π : String → Option Core.Procedure} {F : Core.Expression.Factory}
    (hF : F.factory = Core.Factory) {nv : Int} (hnv : 0 ≤ nv)
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : RunInv F nv before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    RunInv F nv after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans entry_lookup)
      rw [hb]
      exact ⟨RunInv.entryPreInitI ρ hf h, rfl⟩
  | entryPreInitI ρ hf h =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hother, rfl⟩ := init_inv hcmd
      exact ⟨RunInv.entryPreInitS _ hf ((hother nId i_ne_n).trans h), rfl⟩
  | entryPreInitS ρ hf h =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hother, rfl⟩ := init_inv hcmd
      exact ⟨RunInv.entryPreSetI0 _ hf ((hother nId s_ne_n).trans h), rfl⟩
  | entryPreSetI0 ρ hf h =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F 0 :=
        Option.some.inj (heval.symm.trans (Core.eval_const F ρ.store (.intConst 0)))
      subst hv
      exact ⟨RunInv.entryPreSetS0 _ hf ⟨(hother nId i_ne_n).trans h, hres⟩, rfl⟩
  | entryPreSetS0 ρ hf h =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F 0 :=
        Option.some.inj (heval.symm.trans (Core.eval_const F ρ.store (.intConst 0)))
      subst hv
      obtain ⟨hn, hi⟩ := h
      exact ⟨RunInv.entryAtGoto _ hf ⟨0, 0, (hother nId s_ne_n).trans hn,
        (hother iId s_ne_i).trans hi, hres, by decide, hnv⟩, rfl⟩
  | entryAtGoto ρ hf h =>
    cases hstep with
    | goto_true _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
  | atLoop ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans loop_lookup)
      rw [hb]
      exact ⟨RunInv.loopAtBranch ρ hf h, rfl⟩
  | loopAtBranch ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hle⟩ := h
    cases hstep with
    | goto_true hguard =>
      rw [hf] at hguard
      have heq := Option.some.inj (hguard.symm.trans (eval_lt F hF ρ.store iv nv hi hn))
      have hlt : iv < nv := of_decide_eq_true (Lambda.SemValue.ofBool_injective heq).symm
      exact ⟨RunInv.atBody ρ hf ⟨iv, sv, hn, hi, hs, hsum, hlt⟩, rfl⟩
    | goto_false hguard =>
      rw [hf] at hguard
      have heq := Option.some.inj (hguard.symm.trans (eval_lt F hF ρ.store iv nv hi hn))
      have hge : ¬ iv < nv := of_decide_eq_false (Lambda.SemValue.ofBool_injective heq).symm
      exact ⟨RunInv.atDone ρ hf ⟨iv, sv, hn, hi, hs, hsum, by omega⟩, rfl⟩
  | atBody ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans body_lookup)
      rw [hb]
      exact ⟨RunInv.bodyPreInc ρ hf h, rfl⟩
  | bodyPreInc ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hlt⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F (iv + 1) :=
        Option.some.inj (heval.symm.trans (eval_inc F hF ρ.store iv hi))
      subst hv
      exact ⟨RunInv.bodyPreAdd _ hf ⟨iv + 1, sv, (hother nId i_ne_n).trans hn, hres,
        (hother sId i_ne_s).trans hs, by grind, by omega⟩, rfl⟩
  | bodyPreAdd ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hle⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F (sv + iv) :=
        Option.some.inj (heval.symm.trans (eval_add F hF ρ.store sv iv hs hi))
      subst hv
      exact ⟨RunInv.bodyAtGoto _ hf ⟨iv, sv + iv, (hother nId s_ne_n).trans hn,
        (hother iId s_ne_i).trans hi, hres, by grind, hle⟩, rfl⟩
  | bodyAtGoto ρ hf h =>
    cases hstep with
    | goto_true _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
  | atDone ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans done_lookup)
      rw [hb]
      exact ⟨RunInv.donePreSet ρ hf h, rfl⟩
  | donePreSet ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hiv⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F sv :=
        Option.some.inj (heval.symm.trans (Core.eval_fvar_int (ty := intTy) F hs))
      subst hv
      subst hiv
      exact ⟨RunInv.doneAtFinish _ hf ⟨sv, (hother nId result_ne_n).trans hn, hres, hsum⟩, rfl⟩
  | doneAtFinish ρ hf h =>
    cases hstep with
    | finish => exact ⟨RunInv.terminal ρ hf h, rfl⟩
  | terminal ρ hf h =>
    cases hstep

/-- Every run from an invariant state stays in the invariant and emits no events. -/
private theorem run_preserves {π : String → Option Core.Procedure} {F : Core.Expression.Factory}
    (hF : F.factory = Core.Factory) {nv : Int} (hnv : 0 ≤ nv)
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : RunInv F nv start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    RunInv F nv final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ emitted _ rest _ hstep _ ih =>
    obtain ⟨hnext, hem⟩ := step_preserves hF hnv hinv hstep
    obtain ⟨hfinal, hrest⟩ := ih hnext
    subst hem hrest
    exact ⟨hfinal, rfl⟩

/-! ## Reading off the contract -/

private def testParams : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-- The translated `sum_to_n` has a CFG body, namely `sumToNCFG`. -/
private theorem sumToN_body : sumToNProc.body = .cfg sumToNCFG := by native_decide

/-- The procedure named `sum_to_n` resolves to `sumToNProc` in the translated AST. -/
private theorem sumToN_find : sumToNAST.findProcByString? "sum_to_n" = some sumToNProc := by
  native_decide

/-! ## Contract denotation -/

/-- `int.mul(2, _)`'s operand literal. -/
private def twoExpr : Core.Expression.Expr := .const () (.intConst 2)
/-- The arrow type carried by the `int.ge` operator. -/
private def geArrowTy : Lambda.LMonoTy := .arrow .int (.arrow .int .bool)
/-- The arrow type carried by the `int.add`/`int.mul` operators. -/
private def intArrowTy : Lambda.LMonoTy := .arrow .int (.arrow .int .int)
/-- The `int.ge` operator expression. -/
private def geOpE : Core.Expression.Expr := .op () ⟨"Int.Ge", ()⟩ (some geArrowTy)
/-- The `int.add` operator expression. -/
private def addOpE : Core.Expression.Expr := .op () ⟨"Int.Add", ()⟩ (some intArrowTy)
/-- The `int.mul` operator expression. -/
private def mulOpE : Core.Expression.Expr := .op () ⟨"Int.Mul", ()⟩ (some intArrowTy)
/-- The `sum_to_n` precondition expression `int.ge(n, 0)`. -/
private def reqExprSpec : Core.Expression.Expr := .app () (.app () geOpE nExpr) zeroExpr
/-- The `sum_to_n` postcondition expression `int.mul(2, result) == int.mul(n, int.add(n, 1))`. -/
private def ensExprSpec : Core.Expression.Expr :=
  .eq ()
    (.app () (.app () mulOpE twoExpr) resultExpr)
    (.app () (.app () mulOpE nExpr) (.app () (.app () addOpE nExpr) oneExpr))

/-- The semantic `requires` forces `0 ≤ n` on an integer `n` binding. -/
private theorem req_nonneg (ρ : Imperative.Env Core.Expression)
    (nv : Int) (hfac : ρ.factory.factory = Core.Factory)
    (hvn : ρ.store nId = some (intV ρ.factory nv))
    (hpre : Core.Logic.Hoare.Procedure.preAsPredicate Core.Factory sumToNProc ρ) : 0 ≤ nv := by
  obtain ⟨⟨l, c⟩, hmem, _⟩ :
      ∃ p ∈ sumToNProc.spec.preconditions.toList, (Prod.snd p).expr = reqExprSpec := by native_decide
  have hcexpr : c.expr = reqExprSpec := by
    have key : ∀ p ∈ sumToNProc.spec.preconditions.toList, (Prod.snd p).expr = reqExprSpec := by
      native_decide
    exact key (l, c) hmem
  rcases hpre l c hmem (someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store c.expr = some (HasBool.ttVal ρ.factory) at hex
    have hge : Core.Expression.eval ρ.factory ρ.store reqExprSpec =
        some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (nv ≥ 0))) :=
      Core.eval_intGe (by rw [hfac]; exact Core.coreFactory_intGe)
        (Core.eval_fvar_int (ty := intTy) ρ.factory hvn)
        (Core.eval_const ρ.factory ρ.store (.intConst 0))
    rw [hcexpr] at hex
    exact of_decide_eq_true
      (Lambda.SemValue.ofBool_injective (Option.some.inj (hge.symm.trans hex)))
  · exact absurd hfac hne

/-- The final-store fact `2 * result = n * (n + 1)` discharges the semantic `ensures`. -/
private theorem post_holds (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (ρ : Imperative.Env Core.Expression) (hρ : ρ.factory = F)
    (nv rv : Int) (hvn : ρ.store nId = some (intV F nv))
    (hr : ρ.store resultId = some (intV F rv)) (hsum : 2 * rv = nv * (nv + 1)) :
    Core.Logic.Hoare.Procedure.postAsPredicate Core.Factory sumToNProc ρ := by
  intro l c hmem _hattr world
  have hcexpr : c.expr = ensExprSpec := by
    have key : ∀ p ∈ sumToNProc.spec.postconditions.toList, (Prod.snd p).expr = ensExprSpec := by
      native_decide
    exact key (l, c) hmem
  refine Or.inl ⟨by rw [hρ]; exact hF, ?_⟩
  show Core.Expression.eval ρ.factory ρ.store c.expr = some (HasBool.ttVal ρ.factory)
  rw [hcexpr, hρ]
  have hl : Core.Expression.eval F ρ.store
      (.app () (.app () mulOpE twoExpr) resultExpr) = some (intV F (2 * rv)) :=
    Core.eval_intMul (hF ▸ Core.coreFactory_intMul) (Core.eval_const F ρ.store (.intConst 2))
      (Core.eval_fvar_int F hr)
  have hrhs : Core.Expression.eval F ρ.store
      (.app () (.app () mulOpE nExpr) (.app () (.app () addOpE nExpr) oneExpr)) =
        some (intV F (nv * (nv + 1))) :=
    Core.eval_intMul (hF ▸ Core.coreFactory_intMul) (Core.eval_fvar_int F hvn)
      (Core.eval_intAdd (hF ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int F hvn)
        (Core.eval_const F ρ.store (.intConst 1)))
  rw [← hsum] at hrhs
  exact Core.eval_eq_true F hl hrhs

/-- The CFG `sum_to_n` meets its contract. -/
theorem sum_to_n_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple sumToNAST testParams "sum_to_n" := by
  have hfactory : sumToNAST.factoryBeforeProcedure "sum_to_n" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨sumToNProc, sumToN_find, by native_decide, ?_⟩
  rw [sumToN_body]
  intro ρEntry ρ₀ ρ' trace hpre hinit hterm
  obtain ⟨hpre, rfl⟩ := hpre
  obtain ⟨hpreP, hfac, _hold, hinput⟩ := hpre
  obtain ⟨vn, hvn, invn⟩ := hinput nId Lambda.LMonoTy.int (by native_decide)
  obtain ⟨nv, hvi⟩ := Lambda.SemValue.exists_ofInt invn
  have htc : vn.tc = ρ₀.factory.model.tcInterp := hinit.storeWellDefined nId vn hvn
  rw [hvi, htc] at hvn
  have hnonneg : 0 ≤ nv := req_nonneg ρ₀ nv hfac hvn hpreP
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE sumToNAST.findProcByString?))
      (.atBlock sumToNCFG sumToNCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  rw [sumToN_cfg_eq] at hrun
  obtain ⟨hfinal, htrace⟩ := run_preserves hfac hnonneg (RunInv.atEntry ρ₀ rfl hvn) hrun
  subst htrace
  refine ⟨True.intro, fun _ => ?_⟩
  obtain ⟨hfac', hpost⟩ := runInv_terminal hfinal
  obtain ⟨rv, hn', hr, hsum⟩ := hpost
  have hresultEntry : (ρ₀.store resultId).isSome :=
    hinit.readWritesDefined resultId (by native_decide) (by native_decide)
  have hnProjected : Imperative.projectStore ρ₀.store ρ'.store nId =
      some (intV ρ₀.factory nv) := by
    simp [Imperative.projectStore, hvn, hn']
  have hresultProjected : Imperative.projectStore ρ₀.store ρ'.store resultId =
      some (intV ρ₀.factory rv) := by
    simp [Imperative.projectStore, hresultEntry, hr]
  exact post_holds ρ₀.factory hfac { ρ' with store := Imperative.projectStore ρ₀.store ρ'.store }
    hfac' nv rv hnProjected hresultProjected hsum

/-! ## Non-vacuity of the CFG contract reading and a `CFGInitEnvWF` witness

`contractTriple` for a CFG body is partial correctness: a diverging body would
satisfy any `ensures`.  The procedure `false_ens` below shows the reading is *not*
vacuously satisfiable for a terminating body.  It has output `result`, a
body-local `.nondet` declaration `var t : int`, and the deliberately false
postcondition `ensures false`.  Its CFG runs to a *terminal* configuration
(`fetch`, the `init`, `finish`), so the false `ensures` cannot be excused by
divergence and the contract is refuted (`false_ens_contract_refuted`).

Discharging the obligation exercises an explicitly constructed
`Core.Logic.CFGInitEnvWF` witness (`false_ens_initEnvWF`): its `initTypesInhabited`
field is proved for the `.nondet` `int` declaration, using the value witness
`int0_valueOfTy`. -/

/-- The body-local variable `t` of the `false_ens` / call fixtures. -/
private def tId : Core.Expression.Ident := ⟨"t", ()⟩

/-- The integer `0` is a value of type `int` in every runtime factory — the witness the
    `initTypesInhabited` field of a `CFGInitEnvWF` needs for a `.nondet int`
    declaration. -/
private theorem int0_valueOfTy (F : Core.Expression.Factory) :
    HasVal.valueOfTy (P := Core.Expression) F (intV F 0) intLTy :=
  ⟨rfl, rfl⟩

/-- `false_ens` written first in readable DDM `Core` syntax: a CFG procedure
    with output `result`, a body-local nondeterministic declaration `var t : int`,
    and the deliberately false postcondition `ensures false`. -/
private def falseEnsPgmSrc : Program :=
#strata
program Core;

// A terminating CFG body with a false `ensures`: `var t : int := *; return`.
procedure false_ens(out result : int)
spec {
  ensures (false);
}
cfg entry {
  entry: {
    var t : int;
    return;
  }
};
#end

/-- The translated one-procedure program containing `false_ens`. -/
private def falseEnsPgm : Core.Program := cstToAST falseEnsPgmSrc
/-- The translated `false_ens` procedure. -/
private def falseEnsProc : Core.Procedure := (falseEnsPgm.findProcByString? "false_ens").get!
/-- The `false_ens` CFG body, projected out of the translated procedure. -/
private def falseEnsCFG : Core.DetCFG :=
  match falseEnsProc.body with | .cfg cfg => cfg | _ => default

/-! The hand-spelled command and CFG shapes used by the `false_ens` and `copy`
semantic proofs carry metadata projected from the translated CFG. Equality with
the DDM-produced shapes is pinned by `native_decide`. -/

/-- The body-local `var t : int := *` command of `false_ens`. -/
private def falseEnsInitT : Core.Command :=
  .cmd (.init tId intLTy .nondet (cmdMdOf falseEnsCFG "entry" 0))

/-- The translated `false_ens` body is the CFG `falseEnsCFG`. -/
private theorem falseEns_body : falseEnsProc.body = .cfg falseEnsCFG := by native_decide
/-- The translated `false_ens` entry block holds the single `var t : int`
    declaration and a `finish` transfer. -/
private theorem falseEns_entry_lookup :
    falseEnsCFG.blocks.lookup falseEnsCFG.entry =
      some { cmds := [falseEnsInitT],
             transfer := .finish (transferMdOf falseEnsCFG "entry") } := by native_decide

/-- The entry environment for the `false_ens` run: the empty store over the runtime
    factory of `model`. -/
private def ρ0N (model : Lambda.Interp Core.Factory) : Imperative.Env Core.Expression :=
  { store := Imperative.emptyStore,
    factory := boolFactory model }

/-- The store after the body-local `var t : int := *` chooses `0`. -/
private def σ2N (model : Lambda.Interp Core.Factory) : Core.CoreStore :=
  fun i => if i = tId then
      some (intV (boolFactory model) 0)
    else Imperative.emptyStore i

/-- Declaring `t := 0` from the empty store is a valid `InitState`. -/
private theorem hinitN (model : Lambda.Interp Core.Factory) :
    Imperative.InitState Core.Expression Imperative.emptyStore tId
      (intV (boolFactory model) 0) (σ2N model) :=
  .init rfl (by simp [σ2N])
    (fun y hy => by
      have hne : y ≠ tId := fun h => hy h.symm
      simp [σ2N, hne])

/-- **An explicit `CFGInitEnvWF` witness for `falseEnsCFG`**, whose
    `initTypesInhabited` field is discharged for the `.nondet int` declaration. -/
private theorem false_ens_initEnvWF (model : Lambda.Interp Core.Factory) :
    Core.Logic.CFGInitEnvWF testParams falseEnsCFG (ρ0N model) where
  toWellFormedSemanticEval := Core.coreFactory_WellFormedSemanticEval _ rfl
  storeWellDefined := by intro x v h; simp [ρ0N, Imperative.emptyStore] at h
  readWritesDefined := by
    intro n hn hnd
    have key : ∀ m ∈ (HasVarsImp.modifiedVars (P := Core.Expression) falseEnsCFG ++
        HasVarsImp.definedVars (P := Core.Expression) falseEnsCFG false ++
        HasVarsImp.readVars (P := Core.Expression) falseEnsCFG),
        m ∈ HasVarsImp.definedVars (P := Core.Expression) falseEnsCFG false := by native_decide
    exact absurd (key n hn) hnd
  defsUndefined := by intro n _; simp [ρ0N, Imperative.emptyStore]
  definedVarsNotReserved := by intro n _ name _ p hp; simp [testParams] at hp
  reservedFresh := by intro n _ name _ p hp; simp [testParams] at hp
  factoryDeclared := by intro nm _; rfl
  initTypesInhabited := by
    intro ty hty
    have hlist : Imperative.DetCFG.initTypes falseEnsCFG = [intLTy] := by native_decide
    rw [hlist] at hty
    simp only [List.mem_singleton] at hty
    subst hty
    exact ⟨intV _ 0, int0_valueOfTy _⟩

/-- The `false_ens` body runs to a terminal configuration, emitting no events. -/
private theorem falseEns_run (model : Lambda.Interp Core.Factory) :
    ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE falseEnsPgm.findProcByString?))
      (.atBlock falseEnsCFG falseEnsCFG.entry (ρ0N model)) []
      (.terminal { ρ0N model with store := σ2N model }) :=
  .step _ [] _ _ _ ((StepCFGE.fetch falseEns_entry_lookup)) <|
  .step _ [] _ _ _ (StepCFGE.step_cmd (EvalCmdExtE.cmd_sem
    (Imperative.EvalCmdE.eval_init_unconstrained (hinitN model) (int0_valueOfTy _)
      (Core.coreEvaluator_WellFormedSemanticEvalVar _)))) <|
  .step _ [] _ [] _ (StepCFGE.finish) (.refl _)

/-- The captured `false` literal never holds under a runtime factory over `Core.Factory`:
    it evaluates to `false`. -/
private theorem ff_not_holds (world : Core.Logic.DenoteValuation Core.Factory)
    (F : Core.Expression.Factory) (hF : F.factory = Core.Factory) (σ : Core.CoreStore)
    (lbl : Core.CoreLabel) (md : Imperative.MetaData Core.Expression) :
    ¬ (Core.Logic.DenoteBasedInterp Core.Factory).holds world
      ⟨F, σ, lbl, Imperative.HasBool.ff, md⟩ := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · exact HasBool.ttVal_ne_ffVal F
      (Option.some.inj (hex.symm.trans (Core.eval_const F σ (.boolConst false))))
  · exact hne hF

/-- The terminating `false_ens` procedure does not meet its contract. -/
theorem false_ens_contract_refuted :
    ¬ Core.Logic.Hoare.Procedure.contractTriple falseEnsPgm testParams "false_ens" := by
  have hfactory : falseEnsPgm.factoryBeforeProcedure "false_ens" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory] at h
  obtain ⟨proc, hfind, _htyped, htriple⟩ := h
  have hpe : proc = falseEnsProc := by
    have hf : falseEnsPgm.findProcByString? "false_ens" = some falseEnsProc := by native_decide
    exact Option.some.inj (hfind.symm.trans hf)
  subst hpe
  have hbody : falseEnsProc.body = .cfg falseEnsCFG := falseEns_body
  rw [hbody] at htriple
  have hpre : Core.Logic.Hoare.Procedure.contractPre Core.Factory falseEnsProc (ρ0N model) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro label check hmem
      rw [show falseEnsProc.spec.preconditions.toList = [] from by native_decide] at hmem
      simp at hmem
    · intro id hid
      rw [show ListMap.keys falseEnsProc.header.getInoutParams = [] from by native_decide] at hid
      simp at hid
    · intro id ty hmem
      rw [show falseEnsProc.header.inputs.toList = [] from by native_decide] at hmem
      simp at hmem
  obtain ⟨_, hpost⟩ := htriple (ρ0N model) (ρ0N model) { ρ0N model with store := σ2N model } []
    ⟨hpre, rfl⟩ (false_ens_initEnvWF model) (Or.inl (falseEns_run model))
  have hreach : Trace.Reachable Core.Expression (Core.Logic.DenoteBasedInterp Core.Factory) [] :=
    ⟨someValuation _, by intro c hc; simp at hc⟩
  obtain ⟨⟨plabel, pcheck⟩, hmem, hattr, hexpr⟩ :
      ∃ lc ∈ falseEnsProc.spec.postconditions.toList,
        (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
        (Prod.snd lc).expr = Imperative.HasBool.ff := by native_decide
  have hcheck := (hpost hreach) plabel pcheck hmem hattr (someValuation _)
  rw [hexpr] at hcheck
  exact ff_not_holds (someValuation _) _ rfl _ plabel _ hcheck

/-! ## `call_of_contract` applied to a CFG-body callee

`copy(x : int, out result : int)` is a CFG procedure whose body is the single
block `result := x; finish`, with contract `ensures result == x`.  We prove its
`contractTriple` (via the configuration invariant `CopyInv`) and its
`bodyFrame` (via `CopyFrame`), then apply `Procedure.call_of_contract` to a call
`call copy(a, out z)` from a structured caller, deriving the meaningful caller
postcondition `z == a` after the output is returned.  The CFG `contractTriple`
already checks its postcondition on the projected final store, and its CFG-body
`hentry` branch is discharged with an explicit `CFGInitEnvWF`. -/

/-- The callee input `x`. -/
private def xIdC : Core.Expression.Ident := ⟨"x", ()⟩
/-- The caller actual input variable `a`. -/
private def aIdC : Core.Expression.Ident := ⟨"a", ()⟩
/-- The caller output variable `z`. -/
private def zIdC : Core.Expression.Ident := ⟨"z", ()⟩
/-- `x` as an expression. -/
private def xExprC : Core.Expression.Expr := .fvar () xIdC intTy
/-- `result == x`, the callee's `ensures`. -/
private def ensExprC : Core.Expression.Expr := Lambda.LExpr.eq () resultExpr xExprC

/-- `copy` written first in readable DDM `Core` syntax: input `x : int`, output
    `result : int`, `ensures result == x`, and a single-block CFG body
    `result := x; return`. -/
private def copyPgmSrc : Program :=
#strata
program Core;

// A CFG callee whose single-block body copies its input to its output.
procedure copy(x : int, out result : int)
spec {
  ensures (result == x);
}
cfg entry {
  entry: {
    result := x;
    return;
  }
};
#end

/-- The translated one-procedure program containing `copy`. -/
private def copyPgm : Core.Program := cstToAST copyPgmSrc
/-- The translated `copy` procedure. -/
private def copyProc : Core.Procedure := (copyPgm.findProcByString? "copy").get!
/-- The `copy` CFG body, projected out of the translated procedure. -/
private def copyCFG : Core.DetCFG :=
  match copyProc.body with | .cfg cfg => cfg | _ => default

/-- The callee body command `result := x` (metadata projected from DDM). -/
private def copySet : Core.Command :=
  .cmd (.set resultId (.det xExprC) (cmdMdOf copyCFG "entry" 0))

/-- The DDM program resolves `copy` to `copyProc`. -/
private theorem copy_find : copyPgm.findProcByString? "copy" = some copyProc := by native_decide
/-- The translated `copy` procedure has CFG body `copyCFG`. -/
private theorem copy_body : copyProc.body = .cfg copyCFG := by native_decide
/-- The translated `copy` CFG's entry label is `"entry"`. -/
private theorem copy_entry : copyCFG.entry = "entry" := by native_decide
/-- The translated `copy` entry block contains the copy assignment and returns. -/
private theorem copy_entry_lookup : copyCFG.blocks.lookup "entry" =
    some { cmds := [copySet], transfer := .finish (transferMdOf copyCFG "entry") } := by
  native_decide
/-- Every postcondition of `copy` is the `result == x` clause. -/
private theorem post_expr_copy : ∀ lc ∈ copyProc.spec.postconditions.toList,
    (Prod.snd lc).expr = ensExprC := by native_decide

/-! ### The callee contract: `CopyInv` and its preservation -/

/-- Reachability invariant for a `copy` run over the runtime factory `F` from entry
    value `x ↦ a`. -/
private inductive CopyInv (F : Core.Expression.Factory) (a : Int) :
    CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (hx : ρ.store xIdC = some (intV F a)) :
      CopyInv F a (.atBlock copyCFG "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (hx : ρ.store xIdC = some (intV F a)) :
      CopyInv F a (.inBlock copyCFG "entry" [copySet] (.finish (transferMdOf copyCFG "entry")) ρ)
  | atFinish (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (hx : ρ.store xIdC = some (intV F a))
      (hr : ρ.store resultId = some (intV F a)) :
      CopyInv F a (.inBlock copyCFG "entry" [] (.finish (transferMdOf copyCFG "entry")) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (hx : ρ.store xIdC = some (intV F a))
      (hr : ρ.store resultId = some (intV F a)) :
      CopyInv F a (.terminal ρ)

/-- One CFG step preserves `CopyInv` and emits no events. -/
private theorem step_preserves_copy {π : String → Option Core.Procedure}
    {F : Core.Expression.Factory} {a : Int}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyInv F a before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyInv F a after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf hx =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyInv.preSet ρ hf hx, rfl⟩
  | preSet ρ hf hx =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = intV F a :=
        Option.some.inj (heval.symm.trans (Core.eval_fvar_int (ty := intTy) F hx))
      subst hv
      exact ⟨CopyInv.atFinish _ hf ((hother xIdC (ident_ne (by decide))).trans hx) hres, rfl⟩
  | atFinish ρ hf hx hr =>
    cases hstep with
    | finish => exact ⟨CopyInv.terminal ρ hf hx hr, rfl⟩
  | terminal ρ hf hx hr =>
    cases hstep

/-- A whole run preserves `CopyInv` and emits no events. -/
private theorem run_preserves_copy {π : String → Option Core.Procedure}
    {F : Core.Expression.Factory} {a : Int}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : CopyInv F a start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    CopyInv F a final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ emitted _ rest _ hstep _ ih =>
    obtain ⟨hnext, hem⟩ := step_preserves_copy hinv hstep
    obtain ⟨hfinal, hrest⟩ := ih hnext
    subst hem hrest
    exact ⟨hfinal, rfl⟩

/-- An `ensures` that equates two variables, each bound to the same value of the
    runtime factory, holds in every world: both sides evaluate to that value, whatever
    model the runtime factory carries. -/
private theorem checkAsPredicate_eq_of_binds (ρ : Imperative.Env Core.Expression)
    (lbl : Core.CoreLabel) (check : Core.Procedure.Check)
    (x y : Core.Expression.Ident) (tyx tyy : Option Lambda.LMonoTy) (v : Core.Expression.Val)
    (hfac : ρ.factory.factory = Core.Factory)
    (hexpr : check.expr =
      Lambda.LExpr.eq () (.fvar () x tyx) (.fvar () y tyy))
    (hx : ρ.store x = some v) (hy : ρ.store y = some v)
    (hv : v.tc = ρ.factory.model.tcInterp) :
    Core.Logic.Hoare.Procedure.checkAsPredicate Core.Factory ρ lbl check := by
  intro world
  refine Or.inl ⟨hfac, ?_⟩
  show Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rw [hexpr]
  exact Core.eval_eq_true _ (Core.eval_fvar _ hx hv) (Core.eval_fvar _ hy hv)

/-- **`copy` meets its contract.**  From input `x`, the CFG body establishes
    `result == x` on the projected final store. -/
theorem copy_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple copyPgm testParams "copy" := by
  have hfactory : copyPgm.factoryBeforeProcedure "copy" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨copyProc, copy_find, by native_decide, ?_⟩
  rw [copy_body]
  intro ρEntry ρ₀ ρ' trace hpre hinit hterm
  obtain ⟨hpre, rfl⟩ := hpre
  obtain ⟨_hpreP, hfac, _hold, hinput⟩ := hpre
  obtain ⟨vx, hvx, hvt⟩ := hinput xIdC Lambda.LMonoTy.int (by native_decide)
  obtain ⟨a, hvi⟩ := Lambda.SemValue.exists_ofInt hvt
  have htc : vx.tc = ρ₀.factory.model.tcInterp := hinit.storeWellDefined xIdC vx hvx
  rw [hvi, htc] at hvx
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE copyPgm.findProcByString?))
      (.atBlock copyCFG copyCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  rw [copy_entry] at hrun
  obtain ⟨hfinal, htrace⟩ := run_preserves_copy (CopyInv.atEntry ρ₀ rfl hvx) hrun
  subst htrace
  cases hfinal with
  | terminal _ hf' hx' hr' =>
    refine ⟨True.intro, fun _ => ?_⟩
    have hxEntry : (ρ₀.store xIdC).isSome :=
      hinit.readWritesDefined xIdC (by native_decide) (by native_decide)
    have hrEntry : (ρ₀.store resultId).isSome :=
      hinit.readWritesDefined resultId (by native_decide) (by native_decide)
    have hxProj : Imperative.projectStore ρ₀.store ρ'.store xIdC =
        some (intV ρ₀.factory a) := by simp [Imperative.projectStore, hxEntry, hx']
    have hrProj : Imperative.projectStore ρ₀.store ρ'.store resultId =
        some (intV ρ₀.factory a) := by simp [Imperative.projectStore, hrEntry, hr']
    intro label check hmem _hattr
    exact checkAsPredicate_eq_of_binds
      { ρ' with store := Imperative.projectStore ρ₀.store ρ'.store } label check
      resultId xIdC intTy intTy (intV ρ₀.factory a)
      ((congrArg (fun F : Core.Expression.Factory => F.factory) hf').trans hfac)
      (post_expr_copy (label, check) hmem) hrProj hxProj
      (congrArg (fun F : Core.Expression.Factory => F.model.tcInterp) hf').symm

/-! ### The callee body frame: `CopyFrame` -/

/-- Frame invariant: at every program point, the running store agrees with the
    entry store `σ_entry` off the output `result`. -/
private inductive CopyFrame (σ_entry : Core.CoreStore) :
    CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hs : ρ.store = σ_entry) :
      CopyFrame σ_entry (.atBlock copyCFG "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hs : ρ.store = σ_entry) :
      CopyFrame σ_entry (.inBlock copyCFG "entry" [copySet] (.finish (transferMdOf copyCFG "entry")) ρ)
  | atFinish (ρ : Env Core.Expression)
      (hfr : Imperative.invStoresExcept σ_entry ρ.store [resultId]) :
      CopyFrame σ_entry (.inBlock copyCFG "entry" [] (.finish (transferMdOf copyCFG "entry")) ρ)
  | terminal (ρ : Env Core.Expression)
      (hfr : Imperative.invStoresExcept σ_entry ρ.store [resultId]) :
      CopyFrame σ_entry (.terminal ρ)

/-- An `UpdateState` writing only `result` gives the entry frame off `result`. -/
private theorem frame_of_update {σ σ' : Core.CoreStore}
    (hother : ∀ y, resultId ≠ y → σ' y = σ y) :
    Imperative.invStoresExcept σ σ' [resultId] :=
  fun vs' hdisj k1 k2 hmem =>
    show σ k1 = σ' k2 from by
      have hk1 : k1 ∈ vs' := (List.of_mem_zip hmem).1
      have hne : resultId ≠ k1 := fun h => hdisj hk1 (List.mem_singleton.mpr h.symm)
      have hk : k1 = k2 := zip_self_eq hmem
      subst hk
      exact (hother k1 hne).symm

/-- `projectStore` preserves the entry frame off `result`. -/
private theorem frame_project {σ_entry σ' : Core.CoreStore}
    (hfr : Imperative.invStoresExcept σ_entry σ' [resultId]) :
    Imperative.invStoresExcept σ_entry (Imperative.projectStore σ_entry σ') [resultId] :=
  fun vs' hdisj k1 k2 hmem =>
    show σ_entry k1 = Imperative.projectStore σ_entry σ' k2 from by
      have heq : σ_entry k1 = σ' k2 := hfr vs' hdisj k1 k2 hmem
      have hk : k1 = k2 := zip_self_eq hmem
      subst hk
      unfold Imperative.projectStore
      by_cases hs : (σ_entry k1).isSome
      · rw [ite_eq_left hs]; exact heq
      · rw [ite_eq_right hs]; exact Option.not_isSome_iff_eq_none.mp hs

/-- One CFG step preserves the `copy` body-frame invariant. -/
private theorem step_preserves_frame {π : String → Option Core.Procedure} {σ_entry : Core.CoreStore}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyFrame σ_entry before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyFrame σ_entry after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hs =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyFrame.preSet ρ hs, rfl⟩
  | preSet ρ hs =>
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨v, _heval, _hres, hother, rfl⟩ := set_inv hcmd
      refine ⟨CopyFrame.atFinish _ ?_, rfl⟩
      rw [← hs]
      exact frame_of_update hother
  | atFinish ρ hfr =>
    cases hstep with
    | finish => exact ⟨CopyFrame.terminal ρ hfr, rfl⟩
  | terminal ρ hfr =>
    cases hstep

/-- Every traced CFG run preserves the `copy` body-frame invariant. -/
private theorem run_preserves_frame {π : String → Option Core.Procedure} {σ_entry : Core.CoreStore}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : CopyFrame σ_entry start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    CopyFrame σ_entry final := by
  induction hrun with
  | refl _ => exact hinv
  | step _ _ _ _ _ hstep _ ih => exact ih (step_preserves_frame hinv hstep).1

/-- **Every `copy` body run respects the output frame `[result]`.** -/
theorem copy_body_frame :
    ∀ proc, copyPgm.findProcByString? "copy" = some proc →
      Core.Logic.Hoare.Procedure.bodyFrame copyPgm.findProcByString? proc := by
  intro proc hlk
  obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
  intro σ_entry fac σ_exit emitted hbody
  rw [copy_body] at hbody
  cases hbody with
  | cfg hrun =>
    rename_i ρ'
    show Imperative.invStoresExcept σ_entry (Imperative.projectStore σ_entry ρ'.store)
      (ListMap.keys copyProc.header.outputs)
    rw [show ListMap.keys copyProc.header.outputs = [resultId] from by native_decide]
    rw [copy_entry] at hrun
    have hfinal := run_preserves_frame (CopyFrame.atEntry ⟨σ_entry, fac⟩ rfl) hrun
    cases hfinal with
    | terminal _ hfr => exact frame_project hfr

/-! ### The callee output typing: `CopyTypedOut` -/

/-- Output-typing invariant for a `copy` run from entry store `σe` at factory
    `fac`, whose input `x` holds the value `w`.  The `atEntry`/`preSet` points pin
    the running store to `σe`; once the `result := x` assignment has fired, the
    invariant records both that `result` was already bound in `σe` (so it survives
    projection) and that it now holds `w`.  The invariant is factory generic:
    `bodyOutputsTyped` must hold at the caller's factory, whatever it is. -/
private inductive CopyTypedOut (fac : Core.Expression.Factory) (σe : Core.CoreStore)
    (w : Core.Expression.Val) :
    CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe)
      (hx : σe xIdC = some w) :
      CopyTypedOut fac σe w (.atBlock copyCFG "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe)
      (hx : σe xIdC = some w) :
      CopyTypedOut fac σe w
        (.inBlock copyCFG "entry" [copySet] (.finish (transferMdOf copyCFG "entry")) ρ)
  | atFinish (ρ : Env Core.Expression) (hf : ρ.factory = fac)
      (hre : (σe resultId).isSome = true)
      (hr : ρ.store resultId = some w) :
      CopyTypedOut fac σe w
        (.inBlock copyCFG "entry" [] (.finish (transferMdOf copyCFG "entry")) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = fac)
      (hre : (σe resultId).isSome = true)
      (hr : ρ.store resultId = some w) :
      CopyTypedOut fac σe w (.terminal ρ)

/-- One CFG step preserves `CopyTypedOut` and emits no events. -/
private theorem step_preserves_typed {π : String → Option Core.Procedure}
    {fac : Core.Expression.Factory} {σe : Core.CoreStore} {w : Core.Expression.Val}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyTypedOut fac σe w before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyTypedOut fac σe w after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf hs hx =>
    cases hstep with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyTypedOut.preSet ρ hf hs hx, rfl⟩
  | preSet ρ hf hs hx =>
    cases hstep with
    | step_cmd hcmd =>
      have hre : (ρ.store resultId).isSome = true := set_pre hcmd
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf, hs] at heval
      rw [hs] at hre
      have hv : v = w := eval_fvar_inv hx heval
      subst hv
      exact ⟨CopyTypedOut.atFinish _ hf hre hres, rfl⟩
  | atFinish ρ hf hre hr =>
    cases hstep with
    | finish => exact ⟨CopyTypedOut.terminal ρ hf hre hr, rfl⟩
  | terminal ρ hf hre hr =>
    cases hstep

/-- A whole run preserves `CopyTypedOut` and emits no events. -/
private theorem run_preserves_typed {π : String → Option Core.Procedure}
    {fac : Core.Expression.Factory} {σe : Core.CoreStore} {w : Core.Expression.Val}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : CopyTypedOut fac σe w start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    CopyTypedOut fac σe w final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ emitted _ rest _ hstep _ ih =>
    obtain ⟨hnext, hem⟩ := step_preserves_typed hinv hstep
    obtain ⟨hfinal, hrest⟩ := ih hnext
    subst hem hrest
    exact ⟨hfinal, rfl⟩

/-- Every `copy` body run binds `result` to a value of its declared type. -/
private theorem copy_body_outputs_typed :
    ∀ proc, copyPgm.findProcByString? "copy" = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped
        (copyPgm.factoryBeforeProcedure "copy") copyPgm.findProcByString? proc := by
  intro proc hlk
  obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
  intro σ_entry fac σ_exit emitted _hfac hin hbody
  obtain ⟨vx, hvx, hvt⟩ := hin xIdC Lambda.LMonoTy.int (by native_decide)
  rw [copy_body] at hbody
  cases hbody with
  | cfg hrun =>
    rename_i ρ'
    rw [copy_entry] at hrun
    obtain ⟨hfinal, _⟩ :=
      run_preserves_typed (CopyTypedOut.atEntry ⟨σ_entry, fac⟩ rfl rfl hvx) hrun
    cases hfinal with
    | terminal _ _hf hre hr =>
      intro id ty hmem
      rw [show copyProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.int)]
        from by native_decide] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      refine ⟨vx, ?_, hvt⟩
      show Imperative.projectStore σ_entry ρ'.store resultId = some vx
      unfold Imperative.projectStore
      rw [ite_eq_left hre]
      exact hr

/-! ### Applying `call_of_contract` to the CFG callee -/

/-- The call `call copy(a, out z)`. -/
private def copyCall : List (Imperative.CallArg Core.Expression) :=
  [.inArg (Lambda.LExpr.fvar () aIdC intTy), .outArg zIdC]

/-- Caller precondition: the runtime factory is over `Core.Factory`, `a` holds an
    integer of it, and `z` is allocated. -/
private def CopyCallPre (ρ : Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ (∃ av, ρ.store aIdC = some (intV ρ.factory av)) ∧
    (ρ.store zIdC).isSome

/-- Caller postcondition: after the call returns, `z == a` evaluates to `true`.
    The callee output `result`, which is written back into `z`, is an integer
    (from `outputAsPredicate`), and the semantic callee equality `result == x`
    pins it to `a`'s value, so the comparison `z == a` evaluates to `true`. -/
private def CopyCallPost (ρ : Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧
    Core.Expression.eval ρ.factory ρ.store
      (Lambda.LExpr.eq () (Lambda.LExpr.fvar () zIdC intTy) (Lambda.LExpr.fvar () aIdC intTy))
      = some (Imperative.HasBool.ttVal ρ.factory)

/-- When `result` and `x` hold values of the same sort, holding their equality in one
    world forces the values to coincide. -/
private theorem resultEq_inv (factory : Lambda.Factory Core.CoreLParams)
    (ρ : Imperative.Env Core.Expression) (lbl : Core.CoreLabel) (check : Core.Procedure.Check)
    (vr vx : Core.Expression.Val) (hfac : ρ.factory.factory = factory)
    (hexpr : check.expr = ensExprC)
    (hr : ρ.store resultId = some vr) (hx : ρ.store xIdC = some vx)
    (hxtc : vx.tc = ρ.factory.model.tcInterp) (hsort : vr.sort = vx.sort)
    (h : Core.Logic.Hoare.Procedure.checkAsPredicate factory ρ lbl check) : vr = vx := by
  rcases h (someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (HasBool.ttVal ρ.factory) at hex
    rw [hexpr] at hex
    obtain ⟨w, hw, hwtc⟩ := Lambda.LExpr.denoteEval_defines hex resultId
      (by simp [ensExprC, resultExpr, xExprC, Lambda.LExpr.LExpr.getVars])
    rw [hr] at hw
    cases hw
    exact Classical.byContradiction fun hne => HasBool.ttVal_ne_ffVal _
      (Option.some.inj (hex.symm.trans (Core.eval_eq_false _ (Core.eval_fvar _ hr hwtc)
        (Core.eval_fvar _ hx hxtc) hsort hne)))
  · exact absurd hfac hne

/-- The callee entry frame `σAO` for `copy(a, out z)` binds `x` to `a`'s value and
    `result` to `z`'s slot value, both values, and is a well-formed store. -/
private theorem copy_callentry_facts
    {ρ₀ : Env Core.Expression} {σAO : Core.CoreStore} {av : Int}
    (ha : ρ₀.store aIdC = some (intV ρ₀.factory av))
    (h : Core.CallEntry ρ₀.factory ρ₀.store copyProc copyCall σAO) :
    σAO xIdC = some (intV ρ₀.factory av) ∧
      (∃ vz, σAO resultId = some vz ∧ HasVal.value ρ₀.factory vz) ∧
      Imperative.WellFormedStore σAO ρ₀.factory := by
  obtain ⟨inputVals, outOnlyVals, hEE, hRV, σA, σIO, hIA, hIO, hSnap⟩ := h
  rw [show Imperative.Calls.getInputExprs copyCall = [Lambda.LExpr.fvar () aIdC intTy] from rfl]
    at hEE
  rw [show Imperative.CallArg.getOutArgs copyCall = [zIdC] from rfl] at hRV
  rw [show Imperative.ProcedureHeader.inputParams (P := Core.Expression) copyProc.header = [xIdC]
    from by native_decide] at hIA
  rw [show Imperative.Calls.outputOnlyParams (P := Core.Expression) copyProc.header = [resultId]
    from by native_decide] at hIO
  have hAOeq : σAO = σIO := by
    rw [hSnap, show Imperative.Calls.inoutParams (P := Core.Expression) copyProc.header = []
      from by native_decide]
    funext id; simp [Imperative.Calls.withOldSnapshots]
  cases hEE with
  | eval_some _hd1 he1 hEE2 =>
    cases hEE2
    have hv1 := eval_fvar_inv ha he1
    subst hv1
    cases hRV with
    | read_some _hz hvz hRV2 =>
      cases hRV2
      have hwfA : Imperative.WellFormedStore σA ρ₀.factory :=
        Imperative.initStates_preserves_wf hIA
          (fun w v hv => by simp [Imperative.emptyStore] at hv)
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              subst hv; rfl)
      have hwfIO : Imperative.WellFormedStore σIO ρ₀.factory :=
        Imperative.initStates_preserves_wf hIO hwfA
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              subst hv; exact hvz)
      cases hIA with
      | init_some hix hIA2 =>
        cases hIA2
        cases hIO with
        | init_some hiy hIO2 =>
          cases hIO2
          cases hix with
          | init _ hix2 _ =>
            cases hiy with
            | init _ hiy2 hiyoth =>
              refine ⟨?_, ⟨_, ?_, hvz⟩, hAOeq ▸ hwfIO⟩
              · rw [hAOeq, hiyoth xIdC (ident_ne (by decide)), hix2]
              · rw [hAOeq]; exact hiy2

/-- **`call_of_contract` for the CFG callee.** The structured call
    `call copy(a, out z)` satisfies the Hoare triple `{CopyCallPre} … {CopyCallPost}`:
    after the call returns, `z == a`. Its CFG-body `hentry` branch is discharged
    with an explicit `CFGInitEnvWF`. -/
theorem copy_call_triple :
    Core.Logic.Hoare.Triple copyPgm.findProcByString? testParams CopyCallPre
      [Core.Statement.call "copy" copyCall .empty] CopyCallPost
      (factory := copyPgm.factoryBeforeProcedure "copy") := by
  have hfactory : copyPgm.factoryBeforeProcedure "copy" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  refine Core.Logic.Hoare.Procedure.call_of_contract copyPgm testParams
    "copy" copyCall .empty CopyCallPre CopyCallPost copy_meets_contract
    copy_body_frame copy_body_outputs_typed ?_ ?_
  · -- hentry
    intro ρ₀ proc σAO hpre hwf hlk hce
    obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
    obtain ⟨hfac, ⟨av, ha⟩, _hz⟩ := hpre
    obtain ⟨hAOx, ⟨vz, hAOr, hvzval⟩, hwfAO⟩ :=
      copy_callentry_facts ha hce
    rw [copy_body]
    refine ⟨⟨?_, hfac.trans hfactory.symm, ?_, ?_⟩, ?_⟩
    · intro label check hmem
      rw [show copyProc.spec.preconditions.toList = [] from by native_decide] at hmem
      simp at hmem
    · intro id hid
      rw [show ListMap.keys copyProc.header.getInoutParams = [] from by native_decide] at hid
      simp at hid
    · intro id ty hmem
      rw [show copyProc.header.inputs.toList = [(xIdC, Lambda.LMonoTy.int)] from by native_decide]
        at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨intV ρ₀.factory av, hAOx, rfl⟩
    · exact
        { toWellFormedSemanticEval := Core.coreFactory_WellFormedSemanticEval _ hfac
          storeWellDefined := hwfAO
          readWritesDefined := by
            intro n hn _hnd
            have key : ∀ m ∈ (HasVarsImp.modifiedVars (P := Core.Expression) copyCFG ++
                HasVarsImp.definedVars (P := Core.Expression) copyCFG false ++
                HasVarsImp.readVars (P := Core.Expression) copyCFG),
                m = resultId ∨ m = xIdC := by native_decide
            rcases key n hn with rfl | rfl
            · simp [hAOr]
            · simp [hAOx]
          defsUndefined := by
            intro n hn
            rw [show HasVarsImp.definedVars (P := Core.Expression) copyCFG false = []
              from by native_decide] at hn
            simp at hn
          definedVarsNotReserved := by
            intro n hn _ _
            rw [show HasVarsImp.definedVars (P := Core.Expression) copyCFG false = []
              from by native_decide] at hn
            simp at hn
          reservedFresh := by intro n _ name _ p hp; simp [testParams] at hp
          factoryDeclared := by intro nm _; rfl
          initTypesInhabited := by
            intro ty hty
            rw [show Imperative.DetCFG.initTypes copyCFG = [] from by native_decide] at hty
            simp at hty }
  · -- hexit
    intro ρ₀ proc ρ' σ' σAO hpre hwf hlk hpost houtputsρ hρ'fac hce hframeRel hcallexit
    obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
    obtain ⟨hfac, ⟨av, ha⟩, _hz⟩ := hpre
    obtain ⟨hAOx, _, _⟩ := copy_callentry_facts ha hce
    have hdisjx : ([xIdC] : List Core.Expression.Ident).Disj
        (ListMap.keys copyProc.header.outputs) := by
      rw [show ListMap.keys copyProc.header.outputs = [resultId] from by native_decide]
      intro a' ha1 ha2
      simp only [List.mem_singleton] at ha1 ha2
      rw [ha1] at ha2; exact absurd ha2 (ident_ne (by decide))
    have hxFinal : ρ'.store xIdC = some (intV ρ₀.factory av) := by
      have hf := hframeRel [xIdC] hdisjx xIdC xIdC (by simp)
      rw [← hf]; exact hAOx
    obtain ⟨vr, hrStore, hvt⟩ := houtputsρ resultId Lambda.LMonoTy.int (by native_decide)
    obtain ⟨⟨plabel, pcheck⟩, hmem, hattr, hpexpr⟩ :
        ∃ lc ∈ copyProc.spec.postconditions.toList,
          (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
          (Prod.snd lc).expr = ensExprC := by native_decide
    have hvr : vr = intV ρ₀.factory av :=
      resultEq_inv _ ρ' plabel pcheck vr (intV ρ₀.factory av)
        ((congrArg (fun F : Core.Expression.Factory => F.factory) hρ'fac).trans
          (hfac.trans hfactory.symm))
        hpexpr hrStore hxFinal
        (congrArg (fun F : Core.Expression.Factory => F.model.tcInterp) hρ'fac).symm
        (Lambda.LSort.toMonoTy_injective (t := .int) hvt)
        (hpost plabel pcheck hmem hattr)
    rw [hvr] at hrStore
    obtain ⟨_, outputVals, hRV, hUpd, -⟩ := hcallexit
    rw [show Imperative.ProcedureHeader.outputParams (P := Core.Expression) copyProc.header
      = [resultId] from by native_decide] at hRV
    rw [show Imperative.CallArg.getLhs copyCall = [zIdC] from rfl] at hUpd
    cases hRV with
    | read_some hres _hvr_val hRV2 =>
      cases hRV2
      cases hUpd with
      | update_some hub hUpd2 =>
        cases hUpd2
        cases hub with
        | update _ hznew hzother =>
          refine ⟨hfac, ?_⟩
          have hzEnd : σ' zIdC = some (intV ρ₀.factory av) := by
            rw [hznew]; exact congrArg some (Option.some.inj (hres.symm.trans hrStore))
          exact Core.eval_eq_true _ (Core.eval_fvar_int (ty := intTy) _ hzEnd)
            (Core.eval_fvar_int _ (show σ' aIdC = some (intV ρ₀.factory av) by
              rw [hzother aIdC (ident_ne (by decide))]; exact ha))

end Strata
