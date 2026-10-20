/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import Strata.Languages.Core.IntEvalProps

import Strata.Languages.Core
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
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

set_option linter.unusedSimpArgs false

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

/-! ## Expression evaluation on `Core.Factory` -/

/-- A free variable bound to an integer constant `k` in the store fully evaluates to
    `intConst k`. -/
private theorem eval_fvar_int (σ : SemanticStore Core.Expression) (x : Core.Expression.Ident)
    (ty : Option Lambda.LMonoTy) (k : Int) (hx : σ x = some (.intConst () k)) :
    Lambda.LExpr.evalFully Core.Factory σ (.fvar () x ty) = some (Lambda.LExpr.intConst () k) :=
  Lambda.evalFully_fvar_of_value Core.Factory σ () x ty _ hx
    (Lambda.isValue_const_true _ _ _)

/-- Factory-generic version of `eval_fvar_int`: a free variable bound to an
    integer constant `k` evaluates to `intConst k` in *every* factory `F`, since a
    literal is a value in any factory. -/
private theorem evalFully_fvar_int_gen (F : Core.Expression.Factory)
    (σ : SemanticStore Core.Expression) (x : Core.Expression.Ident)
    (ty : Option Lambda.LMonoTy) (k : Int) (hx : σ x = some (.intConst () k)) :
    Lambda.LExpr.evalFully F σ (.fvar () x ty) = some (Lambda.LExpr.intConst () k) :=
  Lambda.evalFully_fvar_of_value F σ () x ty _ hx
    (Lambda.isValue_const_true _ _ _)

/-- `int.lt(i, n)` with `i ↦ a`, `n ↦ b` evaluates to `boolConst (a < b)`. -/
private theorem eval_lt (σ : SemanticStore Core.Expression) (a b : Int)
    (hi : σ iId = some (.intConst () a)) (hn : σ nId = some (.intConst () b)) :
    Core.Expression.eval Core.Factory σ ltExpr
      = some (Lambda.LExpr.boolConst () (decide (a < b))) := by
  have hiv := eval_fvar_int σ iId intTy a hi
  have hnv := eval_fvar_int σ nId intTy b hn
  obtain ⟨ni, hni, _⟩ := Lambda.evalFully_some_exists Core.Factory σ _ _ hiv
  obtain ⟨nn, hnn, _⟩ := Lambda.evalFully_some_exists Core.Factory σ _ _ hnv
  have hi_max := Lambda.eval_value_true_mono_le Core.Factory σ ni (max ni nn)
    (Nat.le_max_left _ _) _ _ hni
  have hn_max := Lambda.eval_value_true_mono_le Core.Factory σ nn (max ni nn)
    (Nat.le_max_right _ _) _ _ hnn
  have hstep := Core.eval_intLt_value_of_numerals Core.Factory σ iExpr nExpr
    (max ni nn) a b Core.coreFactory_intLt hi_max hn_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

/-- `int.add(s, i)` with `s ↦ a`, `i ↦ b` evaluates to `intConst (a + b)`. -/
private theorem eval_add (σ : SemanticStore Core.Expression) (a b : Int)
    (hs : σ sId = some (.intConst () a)) (hi : σ iId = some (.intConst () b)) :
    Core.Expression.eval Core.Factory σ addExpr = some (Lambda.LExpr.intConst () (a + b)) := by
  have hsv := eval_fvar_int σ sId intTy a hs
  have hiv := eval_fvar_int σ iId intTy b hi
  obtain ⟨ns, hns, _⟩ := Lambda.evalFully_some_exists Core.Factory σ _ _ hsv
  obtain ⟨ni, hni, _⟩ := Lambda.evalFully_some_exists Core.Factory σ _ _ hiv
  have hs_max := Lambda.eval_value_true_mono_le Core.Factory σ ns (max ns ni)
    (Nat.le_max_left _ _) _ _ hns
  have hi_max := Lambda.eval_value_true_mono_le Core.Factory σ ni (max ns ni)
    (Nat.le_max_right _ _) _ _ hni
  have hstep := Core.eval_intAdd_value_of_numerals Core.Factory σ sExpr iExpr
    (max ns ni) a b Core.coreFactory_intAdd hs_max hi_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

/-- `int.add(i, 1)` with `i ↦ a` evaluates to `intConst (a + 1)`. -/
private theorem eval_inc (σ : SemanticStore Core.Expression) (a : Int)
    (hi : σ iId = some (.intConst () a)) :
    Core.Expression.eval Core.Factory σ incExpr = some (Lambda.LExpr.intConst () (a + 1)) :=
  Core.coreEval_intAdd_numeral σ iExpr a (eval_fvar_int σ iId intTy a hi)

/-! ## The configuration invariant -/

/-- `n` is in the store. -/
private def EntryInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  σ nId = some (.intConst () nv)
/-- `n` is in the store and `i = 0`. -/
private def HalfInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  σ nId = some (.intConst () nv) ∧ σ iId = some (.intConst () 0)
/-- The loop invariant: `2 * s = i * (i + 1)` and `i ≤ n`. -/
private def LoopInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  ∃ iv sv : Int, σ nId = some (.intConst () nv) ∧ σ iId = some (.intConst () iv) ∧
    σ sId = some (.intConst () sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv ≤ nv
/-- Entering the body: the loop invariant and `i < n`. -/
private def BodyInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  ∃ iv sv : Int, σ nId = some (.intConst () nv) ∧ σ iId = some (.intConst () iv) ∧
    σ sId = some (.intConst () sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv < nv
/-- Between the two body assignments: `i` has been incremented, `s` not yet. -/
private def MidInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  ∃ iv sv : Int, σ nId = some (.intConst () nv) ∧ σ iId = some (.intConst () iv) ∧
    σ sId = some (.intConst () sv) ∧ 2 * sv = (iv - 1) * iv ∧ iv ≤ nv
/-- Loop exit: the loop invariant and `i = n`. -/
private def DoneInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  ∃ iv sv : Int, σ nId = some (.intConst () nv) ∧ σ iId = some (.intConst () iv) ∧
    σ sId = some (.intConst () sv) ∧ 2 * sv = iv * (iv + 1) ∧ iv = nv
/-- After `result := s`. -/
private def PostInv (nv : Int) (σ : SemanticStore Core.Expression) : Prop :=
  ∃ rv : Int, σ nId = some (.intConst () nv) ∧ σ resultId = some (.intConst () rv) ∧
    2 * rv = nv * (nv + 1)

/-- Every configuration reachable from `atBlock "entry"`, with the store facts that hold
    there.  Non-terminal configurations pin the active CFG to `expectedCFG` and the
    factory to `Core.Factory`.  Each constructor names one program point of the
    `sum_to_n` CFG run. -/
private inductive RunInv (nv : Int) :
    CFGConfig String Core.Command Core.Expression → Prop where
  /-- `atBlock "entry"` (about to fetch the entry block). -/
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (h : EntryInv nv ρ.store) :
      RunInv nv (.atBlock expectedCFG "entry" ρ)
  /-- `inBlock "entry"` before any entry command has run. -/
  | entryPreInitI (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : EntryInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "entry" [initI, initS, setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after `var i`, before `var s`. -/
  | entryPreInitS (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : EntryInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "entry" [initS, setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after both `var` declarations, before `i := 0`. -/
  | entryPreSetI0 (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : EntryInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "entry" [setI0, setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after `i := 0`, before `s := 0` (here `HalfInv` additionally
      records `i = 0`). -/
  | entryPreSetS0 (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : HalfInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "entry" [setS0]
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `inBlock "entry"` after both assignments, at the `goto loop` transfer (the loop
      invariant now holds). -/
  | entryAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : LoopInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "entry" []
        (.condGoto trueExpr "loop" "loop" entryMd) ρ)
  /-- `atBlock "loop"` (about to fetch the loop header). -/
  | atLoop (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (h : LoopInv nv ρ.store) :
      RunInv nv (.atBlock expectedCFG "loop" ρ)
  /-- `inBlock "loop"` at the `branch (int.lt(i, n))` transfer. -/
  | loopAtBranch (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : LoopInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "loop" []
        (.condGoto ltExpr "body" "done" loopMd) ρ)
  /-- `atBlock "body"` on the loop-taken branch (`i < n`). -/
  | atBody (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (h : BodyInv nv ρ.store) :
      RunInv nv (.atBlock expectedCFG "body" ρ)
  /-- `inBlock "body"` before `i := int.add(i, 1)`. -/
  | bodyPreInc (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : BodyInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "body" [setIInc, setSAdd]
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `inBlock "body"` after `i` is incremented, before `s := int.add(s, i)`
      (`MidInv`: `s` not yet updated). -/
  | bodyPreAdd (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : MidInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "body" [setSAdd]
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `inBlock "body"` at the backward `goto loop` transfer (the loop invariant is
      re-established). -/
  | bodyAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : LoopInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "body" []
        (.condGoto trueExpr "loop" "loop" bodyMd) ρ)
  /-- `atBlock "done"` on the loop-exit branch (`i = n`). -/
  | atDone (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (h : DoneInv nv ρ.store) :
      RunInv nv (.atBlock expectedCFG "done" ρ)
  /-- `inBlock "done"` before `result := s`. -/
  | donePreSet (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : DoneInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "done" [setResult] (.finish doneMd) ρ)
  /-- `inBlock "done"` after `result := s`, at the `finish` transfer (`PostInv` now
      holds). -/
  | doneAtFinish (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (h : PostInv nv ρ.store) :
      RunInv nv (.inBlock expectedCFG "done" [] (.finish doneMd) ρ)
  /-- The `terminal` configuration (`PostInv` on the final store). -/
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (h : PostInv nv ρ.store) :
      RunInv nv (.terminal ρ)


/-- A terminal configuration satisfying `RunInv` carries the factory fact and `PostInv`. -/
private theorem runInv_terminal {nv : Int} {ρ : Env Core.Expression}
    (h : RunInv nv (.terminal ρ)) : ρ.factory = Core.Factory ∧ PostInv nv ρ.store := by
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
private theorem step_preserves {π : String → Option Core.Procedure} {nv : Int} (hnv : 0 ≤ nv)
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : RunInv nv before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    RunInv nv after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans entry_lookup)
      rw [hb]
      exact ⟨RunInv.entryPreInitI ρ hf h, rfl⟩
  | entryPreInitI ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨hother, rfl⟩ := init_inv hcmd
      exact ⟨RunInv.entryPreInitS _ hf ((hother nId i_ne_n).trans h), rfl⟩
  | entryPreInitS ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨hother, rfl⟩ := init_inv hcmd
      exact ⟨RunInv.entryPreSetI0 _ hf ((hother nId s_ne_n).trans h), rfl⟩
  | entryPreSetI0 ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = .const () (.intConst 0) :=
        Option.some.inj (heval.symm.trans
          (Lambda.evalFully_const Core.Factory ρ.store () (Lambda.LConst.intConst 0)))
      subst hv
      exact ⟨RunInv.entryPreSetS0 _ hf ⟨(hother nId i_ne_n).trans h, hres⟩, rfl⟩
  | entryPreSetS0 ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = .const () (.intConst 0) :=
        Option.some.inj (heval.symm.trans
          (Lambda.evalFully_const Core.Factory ρ.store () (Lambda.LConst.intConst 0)))
      subst hv
      obtain ⟨hn, hi⟩ := h
      exact ⟨RunInv.entryAtGoto _ hf ⟨0, 0, (hother nId s_ne_n).trans hn,
        (hother iId s_ne_i).trans hi, hres, by decide, hnv⟩, rfl⟩
  | entryAtGoto ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | goto_true _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
  | atLoop ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans loop_lookup)
      rw [hb]
      exact ⟨RunInv.loopAtBranch ρ hf h, rfl⟩
  | loopAtBranch ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hle⟩ := h
    cases hstep using StepCFGE.casesRules with
    | goto_true hguard =>
      rw [hf] at hguard
      have heq := Option.some.inj (hguard.symm.trans (eval_lt ρ.store iv nv hi hn))
      have hlt : iv < nv := by
        by_cases hc : iv < nv
        · exact hc
        · rw [decide_eq_false hc] at heq
          exact absurd heq (by decide)
      exact ⟨RunInv.atBody ρ hf ⟨iv, sv, hn, hi, hs, hsum, hlt⟩, rfl⟩
    | goto_false hguard =>
      rw [hf] at hguard
      have heq := Option.some.inj (hguard.symm.trans (eval_lt ρ.store iv nv hi hn))
      have hge : ¬ iv < nv := by
        intro hc
        rw [decide_eq_true hc] at heq
        exact absurd heq (by decide)
      exact ⟨RunInv.atDone ρ hf ⟨iv, sv, hn, hi, hs, hsum, by omega⟩, rfl⟩
  | atBody ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans body_lookup)
      rw [hb]
      exact ⟨RunInv.bodyPreInc ρ hf h, rfl⟩
  | bodyPreInc ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hlt⟩ := h
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = Lambda.LExpr.intConst () (iv + 1) :=
        Option.some.inj (heval.symm.trans (eval_inc ρ.store iv hi))
      subst hv
      exact ⟨RunInv.bodyPreAdd _ hf ⟨iv + 1, sv, (hother nId i_ne_n).trans hn, hres,
        (hother sId i_ne_s).trans hs, by grind, by omega⟩, rfl⟩
  | bodyPreAdd ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hle⟩ := h
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = Lambda.LExpr.intConst () (sv + iv) :=
        Option.some.inj (heval.symm.trans (eval_add ρ.store sv iv hs hi))
      subst hv
      exact ⟨RunInv.bodyAtGoto _ hf ⟨iv, sv + iv, (hother nId s_ne_n).trans hn,
        (hother iId s_ne_i).trans hi, hres, by grind, hle⟩, rfl⟩
  | bodyAtGoto ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | goto_true _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨RunInv.atLoop ρ hf h, rfl⟩
  | atDone ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans done_lookup)
      rw [hb]
      exact ⟨RunInv.donePreSet ρ hf h, rfl⟩
  | donePreSet ρ hf h =>
    obtain ⟨iv, sv, hn, hi, hs, hsum, hiv⟩ := h
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = Lambda.LExpr.intConst () sv :=
        Option.some.inj (heval.symm.trans (eval_fvar_int ρ.store sId intTy sv hs))
      subst hv
      subst hiv
      exact ⟨RunInv.doneAtFinish _ hf ⟨sv, (hother nId result_ne_n).trans hn, hres, hsum⟩, rfl⟩
  | doneAtFinish ρ hf h =>
    cases hstep using StepCFGE.casesRules with
    | finish => exact ⟨RunInv.terminal ρ hf h, rfl⟩
  | terminal ρ hf h =>
    cases hstep using StepCFGE.casesRules

/-- Every run from an invariant state stays in the invariant and emits no events. -/
private theorem run_preserves {π : String → Option Core.Procedure} {nv : Int} (hnv : 0 ≤ nv)
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : RunInv nv start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    RunInv nv final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ emitted _ rest _ hstep _ ih =>
    obtain ⟨hnext, hem⟩ := step_preserves hnv hinv hstep
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

/-- `Lambda.LExpr.intConst` unfolds to a `.const` node. -/
private theorem ic_eq (k : Int) :
    (Lambda.LExpr.intConst () k : Core.Expression.Expr) = .const () (.intConst k) := rfl

/-- The captured `int.ge(n, 0)` with `n ↦ nv` denotes to `nv ≥ 0`. -/
private theorem denote_capReq (model : Lambda.Interp Core.Factory)
    (fvarVal : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (nv : Int)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () geOpE (.const () (.intConst nv))) (.const () (.intConst 0))) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fvarVal vt .nil
      (.app () (.app () geOpE (.const () (.intConst nv))) (.const () (.intConst 0))) .bool h : Bool)
      = decide (nv ≥ 0) := by
  have hic : ∀ (i : Int) (hh : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.const () (.intConst i)) Lambda.LMonoTy.int),
      Lambda.LExpr.denote model.tcInterp model.opInterp fvarVal vt .nil
        (.const () (.intConst i)) Lambda.LMonoTy.int hh = i :=
    fun i hh => Lambda.denote_intConst _ _ _ _ _ hh
  have hop : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.op () ⟨"Int.Ge", ()⟩ (some geArrowTy)) (Lambda.LMonoTy.arrow .int (.arrow .int .bool)) := .op
  have hnv : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst nv)) .int := .const
  have hz : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst 0)) .int := .const
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.op () ⟨"Int.Ge", ()⟩ (some geArrowTy)) (.const () (.intConst nv))) (.arrow .int .bool) :=
    .app hop hnv
  simp only [geOpE] at h ⊢
  rw [Lambda.denote_app .nil happ1 hz h, Lambda.denote_app .nil hop hnv happ1]
  simp only [hic]
  rw [Lambda.denote_op]
  show (model.opInterp "Int.Ge"
    (Lambda.LSort.mkArrow .bool [.int, .int]) nv (0 : Int) : Bool)
    = decide (nv ≥ 0)
  rw [Core.intGe_opInterp model nv 0]

/-- The captured `int.mul(2, result) == int.mul(n, int.add(n, 1))` with `n ↦ nv`,
    `result ↦ rv` denotes to `true` whenever `2 * rv = nv * (nv + 1)`. -/
private theorem denote_capEns (model : Lambda.Interp Core.Factory)
    (fvarVal : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (nv rv : Int) (hsum : 2 * rv = nv * (nv + 1))
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.eq ()
        (.app () (.app () mulOpE (.const () (.intConst 2))) (.const () (.intConst rv)))
        (.app () (.app () mulOpE (.const () (.intConst nv)))
          (.app () (.app () addOpE (.const () (.intConst nv))) (.const () (.intConst 1))))) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fvarVal vt .nil
      (.eq ()
        (.app () (.app () mulOpE (.const () (.intConst 2))) (.const () (.intConst rv)))
        (.app () (.app () mulOpE (.const () (.intConst nv)))
          (.app () (.app () addOpE (.const () (.intConst nv))) (.const () (.intConst 1))))) .bool h : Bool)
      = true := by
  have hic : ∀ (i : Int) (hh : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.const () (.intConst i)) Lambda.LMonoTy.int),
      Lambda.LExpr.denote model.tcInterp model.opInterp fvarVal vt .nil
        (.const () (.intConst i)) Lambda.LMonoTy.int hh = i :=
    fun i hh => Lambda.denote_intConst _ _ _ _ _ hh
  have hmulOp : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.op () ⟨"Int.Mul", ()⟩ (some intArrowTy)) (Lambda.LMonoTy.arrow .int (.arrow .int .int)) := .op
  have haddOp : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.op () ⟨"Int.Add", ()⟩ (some intArrowTy)) (Lambda.LMonoTy.arrow .int (.arrow .int .int)) := .op
  have h2 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst 2)) .int := .const
  have hrv : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst rv)) .int := .const
  have hnv : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst nv)) .int := .const
  have h1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (.const () (.intConst 1)) .int := .const
  have hlhs1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.op () ⟨"Int.Mul", ()⟩ (some intArrowTy)) (.const () (.intConst 2))) (.arrow .int .int) := .app hmulOp h2
  have hlhs : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () (.op () ⟨"Int.Mul", ()⟩ (some intArrowTy)) (.const () (.intConst 2))) (.const () (.intConst rv))) .int := .app hlhs1 hrv
  have hadd1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.op () ⟨"Int.Add", ()⟩ (some intArrowTy)) (.const () (.intConst nv))) (.arrow .int .int) := .app haddOp hnv
  have hadd : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intArrowTy)) (.const () (.intConst nv))) (.const () (.intConst 1))) .int := .app hadd1 h1
  have hrhs1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.op () ⟨"Int.Mul", ()⟩ (some intArrowTy)) (.const () (.intConst nv))) (.arrow .int .int) := .app hmulOp hnv
  have hrhs : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () (.op () ⟨"Int.Mul", ()⟩ (some intArrowTy)) (.const () (.intConst nv)))
        (.app () (.app () (.op () ⟨"Int.Add", ()⟩ (some intArrowTy)) (.const () (.intConst nv))) (.const () (.intConst 1)))) .int := .app hrhs1 hadd
  simp only [mulOpE, addOpE] at h ⊢
  apply Lambda.denote_eq_true .nil hlhs hrhs h
  rw [Lambda.denote_app .nil hlhs1 hrv hlhs, Lambda.denote_app .nil hmulOp h2 hlhs1,
      Lambda.denote_app .nil hrhs1 hadd hrhs, Lambda.denote_app .nil hmulOp hnv hrhs1,
      Lambda.denote_app .nil hadd1 h1 hadd, Lambda.denote_app .nil haddOp hnv hadd1]
  simp only [hic]
  rw [Lambda.denote_op, Lambda.denote_op]
  show (model.opInterp "Int.Mul"
          (Lambda.LSort.mkArrow .int [.int, .int]) (2 : Int) rv : Int)
      = (model.opInterp "Int.Mul"
          (Lambda.LSort.mkArrow .int [.int, .int]) nv
          (model.opInterp "Int.Add"
            (Lambda.LSort.mkArrow .int [.int, .int]) nv (1 : Int)))
  rw [Core.intMul_opInterp model 2 rv, Core.intAdd_opInterp model nv 1, Core.intMul_opInterp model nv (nv + 1)]
  exact hsum

/-- The semantic `requires` forces `0 ≤ n` on a typed `n` binding. -/
private theorem req_nonneg (model : Lambda.Interp Core.Factory) (ρ : Imperative.Env Core.Expression)
    (nv : Int) (hfac : ρ.factory = Core.Factory) (hvn : ρ.store nId = some (.intConst () nv))
    (hpre : Core.Logic.Hoare.Procedure.preAsPredicate model sumToNProc ρ) : 0 ≤ nv := by
  obtain ⟨⟨l, c⟩, hmem, _⟩ :
      ∃ p ∈ sumToNProc.spec.preconditions.toList, (Prod.snd p).expr = reqExprSpec := by native_decide
  have hcexpr : c.expr = reqExprSpec := by
    have key : ∀ p ∈ sumToNProc.spec.preconditions.toList, (Prod.snd p).expr = reqExprSpec := by
      native_decide
    exact key (l, c) hmem
  rcases hpre l c hmem (someValuation model) with ⟨_, hex⟩ | ⟨hne, _⟩
  · have hcap : Core.Logic.capturedExpr
        { factory := ρ.factory, store := ρ.store, label := l, expr := c.expr, metadata := c.md }
        = .app () (.app () geOpE (.const () (.intConst nv))) (.const () (.intConst 0)) := by
      simp only [Core.Logic.capturedExpr, hcexpr, reqExprSpec, geOpE, nExpr, zeroExpr,
        Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hvn, ic_eq]
    rw [hcap] at hex
    obtain ⟨hty, hd⟩ := hex
    rw [denote_capReq model (someValuation model).freeVarVal (someValuation model).tyVarVal nv hty] at hd
    exact of_decide_eq_true hd
  · exact absurd hfac hne

/-- The final-store fact `2 * result = n * (n + 1)` discharges the semantic `ensures`. -/
private theorem post_holds (model : Lambda.Interp Core.Factory) (ρ : Imperative.Env Core.Expression)
    (nv rv : Int) (hfac : ρ.factory = Core.Factory) (hvn : ρ.store nId = some (.intConst () nv))
    (hr : ρ.store resultId = some (.intConst () rv)) (hsum : 2 * rv = nv * (nv + 1)) :
    Core.Logic.Hoare.Procedure.postAsPredicate model sumToNProc ρ := by
  intro l c hmem _hattr world
  have hcexpr : c.expr = ensExprSpec := by
    have key : ∀ p ∈ sumToNProc.spec.postconditions.toList, (Prod.snd p).expr = ensExprSpec := by
      native_decide
    exact key (l, c) hmem
  have hcap : Core.Logic.capturedExpr
      { factory := ρ.factory, store := ρ.store, label := l, expr := c.expr, metadata := c.md }
      = .eq ()
          (.app () (.app () mulOpE (.const () (.intConst 2))) (.const () (.intConst rv)))
          (.app () (.app () mulOpE (.const () (.intConst nv)))
            (.app () (.app () addOpE (.const () (.intConst nv))) (.const () (.intConst 1)))) := by
    simp only [Core.Logic.capturedExpr, hcexpr, ensExprSpec, mulOpE, addOpE, nExpr, resultExpr,
      twoExpr, oneExpr, Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hvn, hr, ic_eq]
  refine Or.inl ⟨hfac, ?_⟩
  rw [hcap]
  exact ⟨.eq (.app (.app .op .const) .const) (.app (.app .op .const) (.app (.app .op .const) .const)),
    denote_capEns model world.freeVarVal world.tyVarVal nv rv hsum
      (.eq (.app (.app .op .const) .const) (.app (.app .op .const) (.app (.app .op .const) .const)))⟩

/-- The CFG `sum_to_n` meets its contract. -/
theorem sum_to_n_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple sumToNAST testParams "sum_to_n" := by
  refine ⟨sumToNProc, sumToN_find, by native_decide, ?_⟩
  intro model
  rw [sumToN_body]
  intro ρEntry ρ₀ ρ' trace hpre hinit hterm
  obtain ⟨hpre, rfl⟩ := hpre
  obtain ⟨hpreP, hfac, _hold, hinput⟩ := hpre
  obtain ⟨vn, hvn, invn⟩ := hinput nId Lambda.LMonoTy.int (by native_decide)
  obtain ⟨nv, rfl⟩ := invn
  have hnonneg : 0 ≤ nv := req_nonneg model ρ₀ nv hfac hvn hpreP
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE sumToNAST.findProcByString?))
      (.atBlock sumToNCFG sumToNCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  rw [sumToN_cfg_eq] at hrun
  obtain ⟨hfinal, htrace⟩ := run_preserves hnonneg (RunInv.atEntry ρ₀ hfac hvn) hrun
  subst htrace
  refine ⟨True.intro, fun _ => ?_⟩
  obtain ⟨hfac', hpost⟩ := runInv_terminal hfinal
  obtain ⟨rv, hn', hr, hsum⟩ := hpost
  have hresultEntry : (ρ₀.store resultId).isSome :=
    hinit.readWritesDefined resultId (by native_decide) (by native_decide)
  have hnProjected : Imperative.projectStore ρ₀.store ρ'.store nId =
      some (.intConst () nv) := by
    simp [Imperative.projectStore, hvn, hn']
  have hresultProjected : Imperative.projectStore ρ₀.store ρ'.store resultId =
      some (.intConst () rv) := by
    simp [Imperative.projectStore, hresultEntry, hr]
  exact post_holds model { ρ' with store := Imperative.projectStore ρ₀.store ρ'.store }
    nv rv hfac' hnProjected hresultProjected hsum

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

/-- `intConst 0` is a value of type `int` in `Core.Factory` — the witness the
    `initTypesInhabited` field of a `CFGInitEnvWF` needs for a `.nondet int`
    declaration. -/
private theorem int0_valueOfTy :
    HasVal.valueOfTy (P := Core.Expression) Core.Factory (Lambda.LExpr.intConst () 0) intLTy := by
  refine ⟨Lambda.LMonoTy.int, ?_, ?_, ?_⟩ <;> native_decide

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

/-- The entry environment for the `false_ens` run: the empty store at `Core.Factory`. -/
private def ρ0N : Imperative.Env Core.Expression :=
  { store := Imperative.emptyStore, factory := Core.Factory, hasFailure := false }

/-- The store after the body-local `var t : int := *` chooses `0`. -/
private def σ2N : Core.CoreStore :=
  fun i => if i = tId then some (Lambda.LExpr.intConst () 0) else Imperative.emptyStore i

/-- Declaring `t := 0` from the empty store is a valid `InitState`. -/
private theorem hinitN :
    Imperative.InitState Core.Expression Imperative.emptyStore tId
      (Lambda.LExpr.intConst () 0) σ2N :=
  .init rfl (by simp [σ2N])
    (fun y hy => by
      have hne : y ≠ tId := fun h => hy h.symm
      simp [σ2N, hne])

/-- **An explicit `CFGInitEnvWF` witness for `falseEnsCFG`**, whose
    `initTypesInhabited` field is discharged for the `.nondet int` declaration. -/
private theorem false_ens_initEnvWF :
    Core.Logic.CFGInitEnvWF testParams falseEnsCFG ρ0N where
  toWellFormedSemanticEval := Core.coreFactory_WellFormedSemanticEval
  storeWellDefined := by intro x v h; simp [ρ0N, Imperative.emptyStore] at h
  readWritesDefined := by
    intro n hn hnd
    have key : ∀ m ∈ (HasVarsImp.modifiedVars (P := Core.Expression) falseEnsCFG ++
        HasVarsImp.definedVars (P := Core.Expression) falseEnsCFG false ++
        HasVarsImp.readVars (P := Core.Expression) falseEnsCFG),
        m ∈ HasVarsImp.definedVars (P := Core.Expression) falseEnsCFG false := by native_decide
    exact absurd (key n hn) hnd
  defsUndefined := by intro n _; simp [ρ0N, Imperative.emptyStore]
  definedVarsNotReserved := by intro n _ p hp; simp [testParams] at hp
  reservedFresh := by intro n _ p hp; simp [testParams] at hp
  factoryDeclared := by intro nm _; rfl
  initTypesInhabited := by
    intro ty hty
    have hlist : Imperative.DetCFG.initTypes falseEnsCFG = [intLTy] := by native_decide
    rw [hlist] at hty
    simp only [List.mem_singleton] at hty
    subst hty
    exact ⟨Lambda.LExpr.intConst () 0, int0_valueOfTy⟩

/-- The `false_ens` body runs to a terminal configuration, emitting no events. -/
private theorem falseEns_run :
    ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE falseEnsPgm.findProcByString?))
      (.atBlock falseEnsCFG falseEnsCFG.entry ρ0N) [] (.terminal { ρ0N with store := σ2N }) :=
  .step _ [] _ _ _ (StepCFGE.step_admin (Imperative.StepCFG.fetch falseEns_entry_lookup)) <|
  .step _ [] _ _ _ (StepCFGE.step_cmd (EvalCmdExtE.cmd_sem
    (Imperative.EvalCmdE.eval_init_unconstrained hinitN int0_valueOfTy
      (Core.coreEvaluator_WellFormedSemanticEvalVar Core.Factory)))) <|
  .step _ [] _ [] _ (StepCFGE.step_admin Imperative.StepCFG.finish) (.refl _)

/-- The captured `false` literal never holds denotationally at `Core.Factory`:
    its closed captured form denotes `false` in every world. -/
private theorem ff_not_holds (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model) (σ : Core.CoreStore)
    (lbl : Core.CoreLabel) (md : Imperative.MetaData Core.Expression) :
    ¬ (Core.Logic.DenoteBasedInterp model).holds world
      ⟨Core.Factory, σ, lbl, Imperative.HasBool.ff, md⟩ := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · have hcap : Core.Logic.capturedExpr
        (⟨Core.Factory, σ, lbl, Imperative.HasBool.ff, md⟩ :
          Imperative.EventArg Core.Expression) = Imperative.HasBool.ff := by
      simp only [Core.Logic.capturedExpr, Imperative.HasBool.ff, Core.Core.false,
        Lambda.LExpr.boolConst, Lambda.LExpr.substFvarsFromEnv]
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    simp [Imperative.HasBool.ff, Core.Core.false, Lambda.LExpr.boolConst, Lambda.LMonoTy.bool,
      Lambda.denote_boolConst] at hd
  · exact hne rfl

/-- The terminating `false_ens` procedure does not meet its contract. -/
theorem false_ens_contract_refuted :
    ¬ Core.Logic.Hoare.Procedure.contractTriple falseEnsPgm testParams "false_ens" := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  obtain ⟨proc, hfind, _htyped, htriple⟩ := h
  have hpe : proc = falseEnsProc := by
    have hf : falseEnsPgm.findProcByString? "false_ens" = some falseEnsProc := by native_decide
    exact Option.some.inj (hfind.symm.trans hf)
  subst hpe
  have hbody : falseEnsProc.body = .cfg falseEnsCFG := falseEns_body
  rw [hbody] at htriple
  have hpre : Core.Logic.Hoare.Procedure.contractPre model falseEnsProc ρ0N := by
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
  obtain ⟨_, hpost⟩ := htriple model ρ0N ρ0N { ρ0N with store := σ2N } []
    ⟨hpre, rfl⟩ false_ens_initEnvWF (Or.inl falseEns_run)
  have hreach : Trace.Reachable Core.Expression (Core.Logic.DenoteBasedInterp model) [] :=
    ⟨someValuation model, by intro c hc; simp at hc⟩
  obtain ⟨⟨plabel, pcheck⟩, hmem, hattr, hexpr⟩ :
      ∃ lc ∈ falseEnsProc.spec.postconditions.toList,
        (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
        (Prod.snd lc).expr = Imperative.HasBool.ff := by native_decide
  have hcheck := (hpost hreach) plabel pcheck hmem hattr (someValuation model)
  rw [hexpr] at hcheck
  exact ff_not_holds model (someValuation model) _ plabel _ hcheck

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

/-- Reachability invariant for a `copy` run from entry value `x ↦ a`. -/
private inductive CopyInv (a : Int) :
    CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (hx : ρ.store xIdC = some (Lambda.LExpr.intConst () a)) :
      CopyInv a (.atBlock copyCFG "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (hx : ρ.store xIdC = some (Lambda.LExpr.intConst () a)) :
      CopyInv a (.inBlock copyCFG "entry" [copySet] (.finish (transferMdOf copyCFG "entry")) ρ)
  | atFinish (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (hx : ρ.store xIdC = some (Lambda.LExpr.intConst () a))
      (hr : ρ.store resultId = some (Lambda.LExpr.intConst () a)) :
      CopyInv a (.inBlock copyCFG "entry" [] (.finish (transferMdOf copyCFG "entry")) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
      (hx : ρ.store xIdC = some (Lambda.LExpr.intConst () a))
      (hr : ρ.store resultId = some (Lambda.LExpr.intConst () a)) :
      CopyInv a (.terminal ρ)

/-- One CFG step preserves `CopyInv` and emits no events. -/
private theorem step_preserves_copy {π : String → Option Core.Procedure} {a : Int}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyInv a before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyInv a after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf hx =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyInv.preSet ρ hf hx, rfl⟩
  | preSet ρ hf hx =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf] at heval
      have hv : v = Lambda.LExpr.intConst () a :=
        Option.some.inj (heval.symm.trans (eval_fvar_int ρ.store xIdC intTy a hx))
      subst hv
      exact ⟨CopyInv.atFinish _ hf ((hother xIdC (ident_ne (by decide))).trans hx) hres, rfl⟩
  | atFinish ρ hf hx hr =>
    cases hstep using StepCFGE.casesRules with
    | finish => exact ⟨CopyInv.terminal ρ hf hx hr, rfl⟩
  | terminal ρ hf hx hr =>
    cases hstep using StepCFGE.casesRules

/-- A whole run preserves `CopyInv` and emits no events. -/
private theorem run_preserves_copy {π : String → Option Core.Procedure} {a : Int}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : CopyInv a start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    CopyInv a final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ emitted _ rest _ hstep _ ih =>
    obtain ⟨hnext, hem⟩ := step_preserves_copy hinv hstep
    obtain ⟨hfinal, hrest⟩ := ih hnext
    subst hem hrest
    exact ⟨hfinal, rfl⟩

/-- An `ensures` that equates two variables, each bound to the same integer value
    in the store, holds denotationally in every world of every model: after store
    substitution both sides are the literal `a`, so the equality denotes to `true`
    regardless of how the model interprets the factory's operators. -/
private theorem checkAsPredicate_eq_of_binds
    (model : Lambda.Interp Core.Factory) (ρ : Imperative.Env Core.Expression)
    (lbl : Core.CoreLabel) (check : Core.Procedure.Check)
    (x y : Core.Expression.Ident) (tyx tyy : Option Lambda.LMonoTy) (a : Int)
    (hfac : ρ.factory = Core.Factory)
    (hexpr : check.expr =
      Lambda.LExpr.eq () (.fvar () x tyx) (.fvar () y tyy))
    (hx : ρ.store x = some (Lambda.LExpr.intConst () a))
    (hy : ρ.store y = some (Lambda.LExpr.intConst () a)) :
    Core.Logic.Hoare.Procedure.checkAsPredicate model ρ lbl check := by
  intro world
  refine Or.inl ⟨hfac, ?_⟩
  simp only [Core.Logic.capturedExpr, hexpr, Lambda.LExpr.substFvarsFromEnv,
    Lambda.Env.mk, hx, hy]
  have hty : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) ([] : List Lambda.LMonoTy)
      (Lambda.LExpr.eq () (Lambda.LExpr.intConst () a) (Lambda.LExpr.intConst () a))
      Lambda.LMonoTy.bool := Lambda.LExpr.typeCheck_to_HasTypeA (by rfl)
  refine ⟨hty, ?_⟩
  cases hty with
  | eq h1 h2 => exact Lambda.denote_eq_true .nil h1 h2 (.eq h1 h2) rfl

/-- **`copy` meets its contract.**  From input `x`, the CFG body establishes
    `result == x` on the projected final store. -/
theorem copy_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple copyPgm testParams "copy" := by
  refine ⟨copyProc, copy_find, by native_decide, ?_⟩
  intro model
  rw [copy_body]
  intro ρEntry ρ₀ ρ' trace hpre hinit hterm
  obtain ⟨hpre, rfl⟩ := hpre
  obtain ⟨_hpreP, hfac, _hold, hinput⟩ := hpre
  obtain ⟨vx, hvx, a, rfl⟩ := hinput xIdC Lambda.LMonoTy.int (by native_decide)
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE copyPgm.findProcByString?))
      (.atBlock copyCFG copyCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  rw [copy_entry] at hrun
  obtain ⟨hfinal, htrace⟩ := run_preserves_copy (CopyInv.atEntry ρ₀ hfac hvx) hrun
  subst htrace
  cases hfinal with
  | terminal _ hf' hx' hr' =>
    refine ⟨True.intro, fun _ => ?_⟩
    have hxEntry : (ρ₀.store xIdC).isSome :=
      hinit.readWritesDefined xIdC (by native_decide) (by native_decide)
    have hrEntry : (ρ₀.store resultId).isSome :=
      hinit.readWritesDefined resultId (by native_decide) (by native_decide)
    have hxProj : Imperative.projectStore ρ₀.store ρ'.store xIdC =
        some (Lambda.LExpr.intConst () a) := by simp [Imperative.projectStore, hxEntry, hx']
    have hrProj : Imperative.projectStore ρ₀.store ρ'.store resultId =
        some (Lambda.LExpr.intConst () a) := by simp [Imperative.projectStore, hrEntry, hr']
    intro label check hmem _hattr
    exact checkAsPredicate_eq_of_binds model
      { ρ' with store := Imperative.projectStore ρ₀.store ρ'.store } label check
      resultId xIdC intTy intTy a hf' (post_expr_copy (label, check) hmem) hrProj hxProj

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
      · rw [if_pos hs]; exact heq
      · rw [if_neg hs]; exact Option.not_isSome_iff_eq_none.mp hs

/-- One CFG step preserves the `copy` body-frame invariant. -/
private theorem step_preserves_frame {π : String → Option Core.Procedure} {σ_entry : Core.CoreStore}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyFrame σ_entry before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyFrame σ_entry after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hs =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyFrame.preSet ρ hs, rfl⟩
  | preSet ρ hs =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      obtain ⟨v, _heval, _hres, hother, rfl⟩ := set_inv hcmd
      refine ⟨CopyFrame.atFinish _ ?_, rfl⟩
      rw [← hs]
      exact frame_of_update hother
  | atFinish ρ hfr =>
    cases hstep using StepCFGE.casesRules with
    | finish => exact ⟨CopyFrame.terminal ρ hfr, rfl⟩
  | terminal ρ hfr =>
    cases hstep using StepCFGE.casesRules

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
    have hfinal := run_preserves_frame (CopyFrame.atEntry ⟨σ_entry, fac, false⟩ rfl) hrun
    cases hfinal with
    | terminal _ hfr => exact frame_project hfr

/-! ### The callee output typing: `CopyTypedOut` -/

/-- Output-typing invariant for a `copy` run from entry store `σe` at factory
    `fac`, whose input `x` holds the integer `a`.  The `atEntry`/`preSet` points
    pin the running store to `σe`; once the `result := x` assignment has fired, the
    invariant records both that `result` was already bound in `σe` (so it survives
    projection) and that it now holds the literal `a`.  The invariant is factory
    generic: `bodyOutputsTyped` must hold at the caller's factory, whatever it is. -/
private inductive CopyTypedOut (fac : Core.Expression.Factory) (σe : Core.CoreStore) (a : Int) :
    CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe)
      (hx : σe xIdC = some (Lambda.LExpr.intConst () a)) :
      CopyTypedOut fac σe a (.atBlock copyCFG "entry" ρ)
  | preSet (ρ : Env Core.Expression) (hf : ρ.factory = fac) (hs : ρ.store = σe)
      (hx : σe xIdC = some (Lambda.LExpr.intConst () a)) :
      CopyTypedOut fac σe a
        (.inBlock copyCFG "entry" [copySet] (.finish (transferMdOf copyCFG "entry")) ρ)
  | atFinish (ρ : Env Core.Expression) (hf : ρ.factory = fac)
      (hre : (σe resultId).isSome = true)
      (hr : ρ.store resultId = some (Lambda.LExpr.intConst () a)) :
      CopyTypedOut fac σe a
        (.inBlock copyCFG "entry" [] (.finish (transferMdOf copyCFG "entry")) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = fac)
      (hre : (σe resultId).isSome = true)
      (hr : ρ.store resultId = some (Lambda.LExpr.intConst () a)) :
      CopyTypedOut fac σe a (.terminal ρ)

/-- One CFG step preserves `CopyTypedOut` and emits no events. -/
private theorem step_preserves_typed {π : String → Option Core.Procedure}
    {fac : Core.Expression.Factory} {σe : Core.CoreStore} {a : Int}
    {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)}
    (hinv : CopyTypedOut fac σe a before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    CopyTypedOut fac σe a after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf hs hx =>
    cases hstep using StepCFGE.casesRules with
    | fetch hlookup =>
      have hb := Option.some.inj (hlookup.symm.trans copy_entry_lookup)
      rw [hb]
      exact ⟨CopyTypedOut.preSet ρ hf hs hx, rfl⟩
  | preSet ρ hf hs hx =>
    cases hstep using StepCFGE.casesRules with
    | step_cmd hcmd =>
      have hre : (ρ.store resultId).isSome = true := set_pre hcmd
      obtain ⟨v, heval, hres, hother, rfl⟩ := set_inv hcmd
      rw [hf, hs] at heval
      rw [hs] at hre
      have hv : v = Lambda.LExpr.intConst () a :=
        Option.some.inj (heval.symm.trans (evalFully_fvar_int_gen fac σe xIdC intTy a hx))
      subst hv
      exact ⟨CopyTypedOut.atFinish _ hf hre hres, rfl⟩
  | atFinish ρ hf hre hr =>
    cases hstep using StepCFGE.casesRules with
    | finish => exact ⟨CopyTypedOut.terminal ρ hf hre hr, rfl⟩
  | terminal ρ hf hre hr =>
    cases hstep using StepCFGE.casesRules

/-- A whole run preserves `CopyTypedOut` and emits no events. -/
private theorem run_preserves_typed {π : String → Option Core.Procedure}
    {fac : Core.Expression.Factory} {σe : Core.CoreStore} {a : Int}
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)}
    (hinv : CopyTypedOut fac σe a start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    CopyTypedOut fac σe a final ∧ trace = [] := by
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
      Core.Logic.Hoare.Procedure.bodyOutputsTyped copyPgm.findProcByString? proc := by
  intro proc hlk
  obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
  intro σ_entry fac σ_exit emitted _hfac hin hbody
  obtain ⟨vx, hvx, hvt⟩ := hin xIdC Lambda.LMonoTy.int (by native_decide)
  obtain ⟨a, rfl⟩ := hvt
  rw [copy_body] at hbody
  cases hbody with
  | cfg hrun =>
    rename_i ρ'
    rw [copy_entry] at hrun
    obtain ⟨hfinal, _⟩ :=
      run_preserves_typed (CopyTypedOut.atEntry ⟨σ_entry, fac, false⟩ rfl rfl hvx) hrun
    cases hfinal with
    | terminal _ _hf hre hr =>
      intro id ty hmem
      rw [show copyProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.int)]
        from by native_decide] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      refine ⟨Lambda.LExpr.intConst () a, ?_, a, rfl⟩
      show Imperative.projectStore σ_entry ρ'.store resultId = some (Lambda.LExpr.intConst () a)
      unfold Imperative.projectStore
      rw [if_pos hre]
      exact hr

/-! ### Applying `call_of_contract` to the CFG callee -/

/-- The call `call copy(a, out z)`. -/
private def copyCall : List (Imperative.CallArg Core.Expression) :=
  [.inArg (Lambda.LExpr.fvar () aIdC intTy), .outArg zIdC]

/-- Caller precondition: `a` holds an integer and `z` is allocated. -/
private def CopyCallPre (ρ : Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧ (∃ av, ρ.store aIdC = some (Lambda.LExpr.intConst () av)) ∧
    (ρ.store zIdC).isSome

/-- Caller postcondition: after the call returns, `z == a` evaluates to `true`.
    The callee output `result`, which is written back into `z`, is a canonical
    integer (from `outputAsPredicate`), and the semantic callee equality
    `result == x` pins it to `a`'s value, so the concrete `eval`-level comparison
    `z == a` reduces to `true`. -/
private def CopyCallPost (ρ : Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧
    Core.Expression.eval Core.Factory ρ.store
      (Lambda.LExpr.eq () (Lambda.LExpr.fvar () zIdC intTy) (Lambda.LExpr.fvar () aIdC intTy))
      = some Imperative.HasBool.tt

/-- When `result` and `x` are bound to integer literals, holding their equality
    denotationally in one world forces the literals to coincide. -/
private theorem resultEq_inv (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Core.Expression) (lbl : Core.CoreLabel) (check : Core.Procedure.Check)
    (i av : Int) (hfac : ρ.factory = Core.Factory) (hexpr : check.expr = ensExprC)
    (hr : ρ.store resultId = some (Lambda.LExpr.intConst () i))
    (hx : ρ.store xIdC = some (Lambda.LExpr.intConst () av))
    (h : Core.Logic.Hoare.Procedure.checkAsPredicate model ρ lbl check) : i = av := by
  rcases h (someValuation model) with ⟨_, hex⟩ | ⟨hne, _⟩
  · have hcap : Core.Logic.capturedExpr
        { factory := ρ.factory, store := ρ.store, label := lbl, expr := check.expr,
          metadata := check.md }
        = Lambda.LExpr.eq () (Lambda.LExpr.intConst () i) (Lambda.LExpr.intConst () av) := by
      simp only [Core.Logic.capturedExpr, hexpr, ensExprC, resultExpr, xExprC,
        Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hr, hx]
    rw [hcap] at hex
    obtain ⟨hty, hd⟩ := hex
    cases hty with
    | eq hleft hright =>
      cases Lambda.HasTypeA.const_inv hleft
      have heq := Lambda.denote_eq_true_implies_eq .nil hleft hright (.eq hleft hright) hd
      have hd1 := Lambda.denote_intConst model.tcInterp model.opInterp
        (someValuation model).freeVarVal (someValuation model).tyVarVal .nil hleft
      have hd2 := Lambda.denote_intConst model.tcInterp model.opInterp
        (someValuation model).freeVarVal (someValuation model).tyVarVal .nil hright
      exact hd1.symm.trans (heq.trans hd2)
  · exact absurd hfac hne

/-- The callee entry frame `σAO` for `copy(a, out z)` binds `x` to `a`'s value and
    `result` to `z`'s slot value, both values, and is a well-formed store. -/
private theorem copy_callentry_facts
    {ρ₀ : Env Core.Expression} {σAO : Core.CoreStore} {av : Int}
    (hfac : ρ₀.factory = Core.Factory)
    (hsem : Imperative.WellFormedSemanticEval (P := Core.Expression) Core.Factory)
    (hwfσ : Imperative.WellFormedStore ρ₀.store Core.Factory)
    (ha : ρ₀.store aIdC = some (Lambda.LExpr.intConst () av))
    (h : Core.CallEntry ρ₀.factory ρ₀.store copyProc copyCall σAO) :
    σAO xIdC = some (Lambda.LExpr.intConst () av) ∧
      (∃ vz, σAO resultId = some vz ∧ Lambda.LExpr.isValue Core.Factory vz = true) ∧
      Imperative.WellFormedStore σAO Core.Factory := by
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
    rw [hfac] at he1
    cases hRV with
    | read_some _hz hvz hRV2 =>
      cases hRV2
      rw [hfac] at hvz
      have hv1val := hsem.val.outputsAreValues _ _ _ hwfσ he1
      have hwfA : Imperative.WellFormedStore σA Core.Factory :=
        Imperative.initStates_preserves_wf hIA
          (fun w v hv => by simp [Imperative.emptyStore] at hv)
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              subst hv; exact hv1val)
      have hwfIO : Imperative.WellFormedStore σIO Core.Factory :=
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
              · rw [hAOeq, hiyoth xIdC (ident_ne (by decide)), hix2, ← he1]
                exact eval_fvar_int ρ₀.store aIdC intTy av ha
              · rw [hAOeq]; exact hiy2

/-- **`call_of_contract` for the CFG callee.** The structured call
    `call copy(a, out z)` satisfies the Hoare triple `{CopyCallPre} … {CopyCallPost}`:
    after the call returns, `z == a`. Its CFG-body `hentry` branch is discharged
    with an explicit `CFGInitEnvWF`. -/
theorem copy_call_triple :
    Core.Logic.Hoare.Triple copyPgm.findProcByString? testParams CopyCallPre
      [Core.Statement.call "copy" copyCall .empty] CopyCallPost := by
  refine Core.Logic.Hoare.Procedure.call_of_contract copyPgm testParams
    "copy" copyCall .empty CopyCallPre CopyCallPost copy_meets_contract
    copy_body_frame copy_body_outputs_typed ?_ ?_
  · -- hentry
    intro model ρ₀ proc σAO hpre hwf hlk hce
    obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
    obtain ⟨hfac, ⟨av, ha⟩, _hz⟩ := hpre
    obtain ⟨hAOx, ⟨vz, hAOr, hvzval⟩, hwfAO⟩ :=
      copy_callentry_facts hfac (hfac ▸ hwf.toWellFormedSemanticEval)
        (hfac ▸ hwf.storeWellDefined) ha hce
    rw [copy_body]
    refine ⟨⟨?_, hfac, ?_, ?_⟩, ?_⟩
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
      exact ⟨Lambda.LExpr.intConst () av, hAOx, av, rfl⟩
    · rw [hfac]
      exact
        { toWellFormedSemanticEval := Core.coreFactory_WellFormedSemanticEval
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
            intro n hn
            rw [show HasVarsImp.definedVars (P := Core.Expression) copyCFG false = []
              from by native_decide] at hn
            simp at hn
          reservedFresh := by intro n _ p hp; simp [testParams] at hp
          factoryDeclared := by intro nm _; rfl
          initTypesInhabited := by
            intro ty hty
            rw [show Imperative.DetCFG.initTypes copyCFG = [] from by native_decide] at hty
            simp at hty }
  · -- hexit
    intro model ρ₀ proc ρ' σ' σAO hpre hwf hlk hpost houtputsρ hρ'fac hce hframeRel hcallexit
    obtain rfl : proc = copyProc := Option.some.inj (hlk.symm.trans copy_find)
    obtain ⟨hfac, ⟨av, ha⟩, _hz⟩ := hpre
    obtain ⟨hAOx, _, _⟩ :=
      copy_callentry_facts hfac (hfac ▸ hwf.toWellFormedSemanticEval)
        (hfac ▸ hwf.storeWellDefined) ha hce
    have hdisjx : ([xIdC] : List Core.Expression.Ident).Disj
        (ListMap.keys copyProc.header.outputs) := by
      rw [show ListMap.keys copyProc.header.outputs = [resultId] from by native_decide]
      intro a' ha1 ha2
      simp only [List.mem_singleton] at ha1 ha2
      rw [ha1] at ha2; exact absurd ha2 (ident_ne (by decide))
    have hxFinal : ρ'.store xIdC = some (Lambda.LExpr.intConst () av) := by
      have hf := hframeRel [xIdC] hdisjx xIdC xIdC (by simp)
      rw [← hf]; exact hAOx
    obtain ⟨vr, hrStore, hvt⟩ := houtputsρ resultId Lambda.LMonoTy.int (by native_decide)
    obtain ⟨i, rfl⟩ := hvt
    obtain ⟨⟨plabel, pcheck⟩, hmem, hattr, hpexpr⟩ :
        ∃ lc ∈ copyProc.spec.postconditions.toList,
          (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
          (Prod.snd lc).expr = ensExprC := by native_decide
    have hiav : i = av :=
      resultEq_inv model ρ' plabel pcheck i av (hρ'fac.trans hfac) hpexpr hrStore hxFinal
        (hpost plabel pcheck hmem hattr)
    rw [hiav] at hrStore
    obtain ⟨_, outputVals, hRV, hUpd⟩ := hcallexit
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
          have hzEnd : σ' zIdC = some (Lambda.LExpr.intConst () av) := by
            rw [hznew]; exact congrArg some (Option.some.inj (hres.symm.trans hrStore))
          have hzEval := eval_fvar_int σ' zIdC intTy av hzEnd
          have haEval := eval_fvar_int σ' aIdC intTy av
            (by rw [hzother aIdC (ident_ne (by decide))]; exact ha)
          exact Lambda.evalFully_eq_self Core.Factory σ' ()
            (Lambda.LExpr.fvar () zIdC intTy) (Lambda.LExpr.fvar () aIdC intTy)
            (Lambda.LExpr.intConst () av) hzEval haEval

end Strata
