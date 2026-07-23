/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

/-!
Confirms the Strata Core program AST has decidable equality by building a
concrete program (with a function, axioms, and a procedure covering commands,
control flow, and specs), then deciding equality against an independently-parsed
copy of the same source. If the `DecidableEq` instances resolve and agree, the
whole AST — `Expression`, `Command`, `Statement`, `Function`, `Procedure`,
`Decl`, `Program` — has working decidable equality.
-/

meta section

namespace Core

open Lambda Strata Lambda.LTy.Syntax
open Std (ToFormat Format format)

private def pgmSrc : StrataDDM.Program :=
#strata
program Core;

const x : int;
axiom [a1]: x == 5;

function f(a: int): int;
axiom [f1]: (forall y : int :: f(y) > y);

procedure P(out ret : int)
  spec {
    ensures [use_f1]: ret > 7;
  }
{
  var t : int;
  if (x > 0) {
    t := f(x);
  } else {
    t := 0;
  }
  ret := t;
};
#end

-- A variant of `pgmSrc`: the procedure's final assignment differs (`ret := 0`
-- instead of `ret := t`), so the two programs must compare unequal.
private def pgmSrcVariant : StrataDDM.Program :=
#strata
program Core;

const x : int;
axiom [a1]: x == 5;

function f(a: int): int;
axiom [f1]: (forall y : int :: f(y) > y);

procedure P(out ret : int)
  spec {
    ensures [use_f1]: ret > 7;
  }
{
  var t : int;
  if (x > 0) {
    t := f(x);
  } else {
    t := 0;
  }
  ret := 0;
};
#end

private def toCore (pgm : StrataDDM.Program) : Except DiagnosticModel Core.Program := do
  let (cst, _errs) := TransM.run Inhabited.default (translateProgram pgm)
  Core.typeCheck { VerifyOptions.default with verbose := .quiet } cst

-- Parse and type-check the same source twice, independently; deciding the two
-- programs equal exercises the whole AST's `DecidableEq`.
#guard
  (match toCore pgmSrc with
   | .ok p1 => (match toCore pgmSrc with | .ok p2 => decide (p1 = p2) | .error _ => false)
   | .error _ => false)

-- Two different programs must compare unequal.
#guard
  (match toCore pgmSrc with
   | .ok p1 => (match toCore pgmSrcVariant with | .ok p3 => decide (p1 ≠ p3) | .error _ => false)
   | .error _ => false)

end Core

end
