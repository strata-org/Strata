/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.Passive.Program
public import Strata.Transform.Passive.LangProps
import Strata.Util.ExceptProps

/-! # Well-scopedness of loop-free lists and failing traces

Vocabulary shared by the WP and SSA phases and their correctness proofs:

* well-scopedness of loop-free statement lists (`WFL`/`WFS1`), its Boolean check
  (`wflB`/`wfs1B`) and its one-pass hash-set version (`wflBH`);
* a failing feasible trace (`Claim`).

Key definitions: `Claim`, `WFL`, `WFS1`, `wflB`, `wflBH`.

Key theorems: `wflBH_eq`, `claim_prepend`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iDE iB iLB iBo iFv iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

/-! ## Failing traces and well-scopedness -/

/-- The locals a statement puts in scope for the rest of its list. -/
@[expose] def topInit : (PStmt P) → List P.Ident
  | .cmd (.cmd (.init x _ _ _)) => [x]
  | _ => []

mutual
/-- Well-scopedness of a loop-free statement list from scope `S`: reads are in scope, an
    `init` declares a local not in scope, a `set` assigns a variable in scope; no loops,
    calls or nondeterministic guards. -/
@[expose] def WFL (Lc : List P.Ident) : List P.Ident → (PStmts P) → Prop
  | _, [] => True
  | S, s :: rest => WFS1 Lc S s ∧ WFL Lc (topInit s ++ S) rest
@[expose] def WFS1 (Lc : List P.Ident) (S : List P.Ident) : (PStmt P) → Prop
  | .cmd (.cmd (.init x _ (.det e) _)) => x ∉ S ∧ x ∈ Lc ∧ ∀ y ∈ exprFV e, y ∈ S
  | .cmd (.cmd (.init x _ .nondet _)) => x ∉ S ∧ x ∈ Lc
  | .cmd (.cmd (.set x (.det e) _)) => x ∈ S ∧ ∀ y ∈ exprFV e, y ∈ S
  | .cmd (.cmd (.set x .nondet _)) => x ∈ S
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    ∀ y ∈ exprFV e, y ∈ S
  | .ite (.det c) tss ess _ => (∀ y ∈ exprFV c, y ∈ S) ∧ WFL Lc S tss ∧ WFL Lc S ess
  | .block _ ss _ => WFL Lc S ss
  | .exit _ _ | .typeDecl _ _ => True
  | _ => False
end

mutual
/-- The Boolean check of well-scopedness (`WFL`) of a loop-free statement list from scope `S`
    with local names `Lc`. -/
@[expose] def wflB (Lc : List P.Ident) : List P.Ident → (PStmts P) → Bool
  | _, [] => true
  | S, s :: rest => wfs1B Lc S s && wflB Lc (topInit s ++ S) rest
/-- The Boolean check of well-scopedness (`WFS1`) of a loop-free statement from scope `S` with
    local names `Lc`. -/
@[expose] def wfs1B (Lc : List P.Ident) (S : List P.Ident) : (PStmt P) → Bool
  | .cmd (.cmd (.init x _ (.det e) _)) =>
    !S.contains x && Lc.contains x && (exprFV e).all S.contains
  | .cmd (.cmd (.init x _ .nondet _)) => !S.contains x && Lc.contains x
  | .cmd (.cmd (.set x (.det e) _)) => S.contains x && (exprFV e).all S.contains
  | .cmd (.cmd (.set x .nondet _)) => S.contains x
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    (exprFV e).all S.contains
  | .ite (.det c) tss ess _ => (exprFV c).all S.contains && wflB Lc S tss && wflB Lc S ess
  | .block _ ss _ => wflB Lc S ss
  | .exit _ _ | .typeDecl _ _ => true
  | _ => false
end

mutual
/-- `wflB` with the scope in a hash map with multiplicities (`ScopeCount`) and the locals in a hash
    set: the scope additions of a list leave scope at its end; `false` at the first failure. -/
@[expose] def wflList (lc : Std.HashSet P.Ident) (b : ScopeCount P) (ss : PStmts P) :
    Option (ScopeCount P) :=
  match wflGo lc b [] ss with
  | some (b, added) => some (added.foldl ScopeCount.dec b)
  | none => none
  termination_by (sizeOf ss, 1)
/-- `wflList` before the scope additions of the list leave scope; `added` collects them. -/
@[expose] def wflGo (lc : Std.HashSet P.Ident) (b : ScopeCount P) (added : List P.Ident) :
    PStmts P → Option (ScopeCount P × List P.Ident)
  | [] => some (b, added)
  | .cmd (.cmd (.init x _ e _)) :: rest =>
    let ok := !b.contains x && lc.contains x &&
      (match e with | .det e => (exprFV e).all b.contains | .nondet => true)
    if ok then wflGo lc (b.inc x) (x :: added) rest else none
  | s :: rest =>
    match wflStmt lc b s with
    | some b => wflGo lc b added rest
    | none => none
  termination_by ss => (sizeOf ss, 0)
/-- `wfs1B` of a statement that is not an `init` (see `wflList`). -/
@[expose] def wflStmt (lc : Std.HashSet P.Ident) (b : ScopeCount P) :
    PStmt P → Option (ScopeCount P)
  | .cmd (.cmd (.set x (.det e) _)) =>
    if b.contains x && (exprFV e).all b.contains then some b else none
  | .cmd (.cmd (.set x .nondet _)) => if b.contains x then some b else none
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    if (exprFV e).all b.contains then some b else none
  | .ite (.det c) tss ess _ =>
    if (exprFV c).all b.contains then
      match wflList lc b tss with
      | some b => wflList lc b ess
      | none => none
    else none
  | .block _ ss _ => wflList lc b ss
  | .exit _ _ | .typeDecl _ _ => some b
  | _ => none
  termination_by s => (sizeOf s, 1)
end

variable {F : P.Factory} {c : P.Expr} {tss ess : PStmts P} {md : MetaData P} {s : PStmt P}
  {rest l : PStmts P} {k : List (PStmts P)} {x : P.Ident} {σ σ2 : SemanticStore P} {r : RE P}
  {t : AssertId P} {tr1 tr2 : List (Event P)} {ss : PStmts P}

/-- `wflB` in one pass with hash sets. -/
@[expose] def wflBH (Lc : List P.Ident) (S : List P.Ident) (ss : PStmts P) : Bool :=
  (wflList (Std.HashSet.ofList Lc) (S.foldl ScopeCount.inc {}) ss).isSome

end -- public section

end WP
end Imperative
