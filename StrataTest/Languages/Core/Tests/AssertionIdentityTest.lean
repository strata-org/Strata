/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.StmtCFGCallSemantics
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.Simplify
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Assertion identity

An assertion is identified by its label and metadata (`Imperative.AssertId`).
Two assertions with one label and one expression at different source positions
have different identifiers, and a phase that rewrites an assertion's expression
but keeps its metadata keeps its identifier. Assertions with one label and equal
metadata share an identifier; the last sections pin the cases where this happens.
-/

namespace Core.AssertionIdentity.Tests

open Strata

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- The structured body of procedure `name` of `p`. -/
private def bodyOf (p : Core.Program) (name : String) : List Core.Statement :=
  match p.findProcByString? name with
  | some proc => match proc.body with
    | .structured ss => ss
    | _ => []
  | none => []

/-- The label and metadata of every assertion identifier of procedure `name`. -/
private def idsOf (p : Core.Program) (name : String) :
    List (String × Imperative.MetaData Core.Expression) :=
  (Core.Statements.collectAssertIds (bodyOf p name)).map fun a => (a.label, a.md)

/-- The expressions of the assertions of procedure `name`, in order. -/
private def assertExprsOf (p : Core.Program) (name : String) : List Core.Expression.Expr :=
  (bodyOf p name).filterMap fun
    | .cmd (.cmd (.assert _ e _)) => some e
    | _ => none

/-! ## One label and one expression, two assertions -/

private def repeatedPgm : StrataDDM.Program :=
#strata
program Core;
procedure p(x : int)
{
  assert [L]: x != 0;
  assert [L]: x != 0;
};
#end

private def repeated : Core.Program := translateCore repeatedPgm

#guard (assertExprsOf repeated "p").length == 2
#guard (assertExprsOf repeated "p")[0]! == (assertExprsOf repeated "p")[1]!
#guard (idsOf repeated "p").length == 2
#guard (idsOf repeated "p")[0]!.1 == (idsOf repeated "p")[1]!.1
#guard (idsOf repeated "p")[0]! != (idsOf repeated "p")[1]!

/-! ## Simplify rewrites the expression and keeps the identifier -/

private def foldablePgm : StrataDDM.Program :=
#strata
program Core;
inline function dup (v : int) : int { int.add(v, v) }
procedure p(x : int)
{
  assert [A]: int.ge(dup(3), x);
};
#end

private def foldable : Core.Program := translateCore foldablePgm

private def simplified? : Except String Core.Program :=
  match Core.Transform.run foldable Core.Simplify.runSimplify
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => .error s!"Simplify failed: {e}"
  | .ok (_changed, program) => .ok program

#guard simplified?.isOk
private def simplified : Core.Program := simplified?.toOption.getD default

#guard (assertExprsOf simplified "p").length == 1
#guard assertExprsOf simplified "p" != assertExprsOf foldable "p"
#guard (idsOf simplified "p").length == 1
#guard idsOf simplified "p" == idsOf foldable "p"

/-! ## Loop invariants with their own source locations

A loop whose metadata records a source location per invariant gives each
invariant that location as its metadata, so two unlabeled invariants have
different identifiers.
-/

private def invProv (start : Nat) : Provenance :=
  .loc (.file "loop.core") { start := ⟨start⟩, stop := ⟨start + 5⟩ }

private def locatedLoop : Core.Statement :=
  .loop (.det (Lambda.LExpr.boolConst () true)) none
    [("", Lambda.LExpr.boolConst () true), ("", Lambda.LExpr.boolConst () true)] []
    (Imperative.MetaData.pushInvariantProvenance
      (Imperative.MetaData.pushInvariantProvenance #[] (invProv 10)) (invProv 20))

#guard (Core.Statements.collectAssertIds [locatedLoop]).map (fun a => (a.label, a.md)) ==
  [("", Imperative.MetaData.ofProvenance (invProv 10)),
   ("", Imperative.MetaData.ofProvenance (invProv 20))]

/-! ## Precondition checks at two call sites

A call emits each non-free precondition of its callee with the clause's site
metadata (`Imperative.Calls.checksAtCall`), so two calls to one procedure at
different source positions emit precondition events with one label and
different identifiers.
-/

private def twoCallsPgm : StrataDDM.Program :=
#strata
program Core;
procedure g(y : int)
spec {
  requires [gpre]: int.gt(y, 0);
}
{ };
procedure f(x : int)
{
  call g(x);
  call g(x);
};
#end

private def twoCalls : Core.Program := translateCore twoCallsPgm

/-- The metadata of every `call` statement of procedure `name`, in order. -/
private def callMdsOf (p : Core.Program) (name : String) :
    List (Imperative.MetaData Core.Expression) :=
  (bodyOf p name).filterMap fun
    | .cmd (.call _ _ md) => some md
    | _ => none

/-- The label and metadata of the precondition events a call to `g` with call
    metadata `md` emits: by `Calls.defaultAssertEvents_label_metadata`, those of the
    non-free clauses of `Calls.checksAtCall md`, whatever the runtime factory and store. -/
private def preIdsAt (md : Imperative.MetaData Core.Expression) :
    List (String × Imperative.MetaData Core.Expression) :=
  match twoCalls.findProcByString? "g" with
  | some g =>
    (Imperative.Calls.checksAtCall md g.spec.preconditions).toList.filterMap fun
      | (label, check) => if check.attr = .Default then some (label, check.md) else none
  | none => []

#guard (callMdsOf twoCalls "f").length == 2
#guard (callMdsOf twoCalls "f")[0]! != (callMdsOf twoCalls "f")[1]!
#guard (preIdsAt (callMdsOf twoCalls "f")[0]!).map (·.1) == ["gpre"]
#guard (preIdsAt (callMdsOf twoCalls "f")[1]!).map (·.1) == ["gpre"]
#guard preIdsAt (callMdsOf twoCalls "f")[0]! != preIdsAt (callMdsOf twoCalls "f")[1]!

/-! ## Shared identifiers

Each case below has two assertions with one label and equal metadata, hence one
identifier:
- a loop written in Core syntax records no per-invariant source location, so its
  unlabeled invariants both carry the loop's metadata;
- PrecondElim numbers the checks of each call argument from 0 and gives them the
  call's metadata, so the first check of two arguments shares label and metadata;
- assertions without metadata are told apart by their label only.
-/

private def twoInvariantsPgm : StrataDDM.Program :=
#strata
program Core;
procedure p(n : int, out i : int)
{
  i := 0;
  while (int.lt(i, n))
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
};
#end

private def twoInvariants : Core.Program := translateCore twoInvariantsPgm

#guard (idsOf twoInvariants "p").length == 2
#guard (idsOf twoInvariants "p")[0]! == (idsOf twoInvariants "p")[1]!

private def callArgsPgm : StrataDDM.Program :=
#strata
program Core;
procedure q(x : int, y : int) { };
procedure p(a : int, b : int)
{
  call q(int.safeDiv(1, a), int.safeDiv(1, b));
};
#end

private def callArgs? : Except String Core.Program :=
  match Core.Transform.run (translateCore callArgsPgm) Core.PrecondElim.precondElim
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => .error s!"PrecondElim failed: {e}"
  | .ok (_changed, program) => .ok program

#guard callArgs?.isOk
private def callArgs : Core.Program := callArgs?.toOption.getD default

#guard (idsOf callArgs "p").map (·.1) ==
  ["call_q_arg_calls_Int.SafeDiv_0", "call_q_arg_calls_Int.SafeDiv_0"]
#guard (idsOf callArgs "p")[0]! == (idsOf callArgs "p")[1]!
#guard (assertExprsOf callArgs "p")[0]! != (assertExprsOf callArgs "p")[1]!

private def unlocated : List Core.Statement :=
  [Core.Statement.assert "L" (Lambda.LExpr.boolConst () true) #[],
   Core.Statement.assert "L" (Lambda.LExpr.boolConst () false) #[]]

#guard (Core.Statements.collectAssertIds unlocated).map (fun a => (a.label, a.md)) ==
  [("L", #[]), ("L", #[])]

end Core.AssertionIdentity.Tests

end
