/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CoreMatch.Verify
import Strata.Languages.CoreMatch.DDMTransform.StrataGen

/-!
Tests for the statement-form translator and procedure spec
translation: the full statement repertoire, `buildArmInits` accessor
calls, requires/ensures handling (with the `free` attribute and
custom labels), and type-translation breadth across bv-widths,
strings, reals, `Map`, `Sequence`, and `arrow` forms.
-/

open Strata Lambda

namespace CoreMatchStatementsAndSpecsTest


/-! Inspection helpers -/

private partial def hasOp (e : LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩) (name : String) : Bool :=
  match e with
  | .op _ ⟨n, _⟩ _     => n == name
  | .app _ f a         => hasOp f name || hasOp a name
  | .abs _ _ _ b       => hasOp b name
  | .quant _ _ _ _ t b => hasOp t name || hasOp b name
  | .ite _ c t f       => hasOp c name || hasOp t name || hasOp f name
  | .eq _ a b          => hasOp a name || hasOp b name
  | _ => false

private partial def stmtHasOp (s : Core.Statement) (name : String) : Bool :=
  match s with
  | .init _ _ rhs _ =>
    match rhs with
    | .det e   => hasOp e name
    | .nondet  => false
  | .set _ rhs _    => hasOp rhs name
  | .assert _ e _   => hasOp e name
  | .assume _ e _   => hasOp e name
  | .ite cond t e _ =>
    let condHas := match cond with
      | .det c   => hasOp c name
      | .nondet  => false
    condHas || (t.any (stmtHasOp · name)) || (e.any (stmtHasOp · name))
  | .block _ ss _   => ss.any (stmtHasOp · name)
  | _ => false

private def parseToCore (p : Strata.Program)
    : Except DiagnosticModel Core.Program :=
  Strata.CoreMatch.Verify.parseToCore p "test"

private def lookupProc (p : Strata.Program) (name : String) : Option Core.Procedure :=
  match parseToCore p with
  | .error _ => none
  | .ok prog =>
    prog.decls.findSome? fun
      | .proc d _ => if d.header.name.name == name then some d else none
      | _ => none

private def parseError? (p : Strata.Program) : Bool :=
  match parseToCore p with
  | .ok _    => false
  | .error _ => true


/-! Full statement repertoire

Build a procedure that uses every statement form CoreMatch translates,
then check the lowered procedure body has the right shape.  This is
the only place these forms are exercised end-to-end. -/

private def pAssertions : Strata.Program :=
#strata
program CoreMatch;

procedure assertions(out r: int)
{
  assume true;
  assert true;
  r := 0;
};
#end

#guard match lookupProc pAssertions "assertions" with
       | some d =>
         match d.body with
         | [_, _, _] => true   -- assume + assert + assignment
         | _ => false
       | none => false

-- The body contains an assert and an assume statement.
#guard match lookupProc pAssertions "assertions" with
       | some d =>
         d.body.any fun
           | .assert _ _ _ => true
           | _ => false
       | none => false

#guard match lookupProc pAssertions "assertions" with
       | some d =>
         d.body.any fun
           | .assume _ _ _ => true
           | _ => false
       | none => false


private def pIfs : Strata.Program :=
#strata
program CoreMatch;

procedure withIf(b : bool, out r: int)
{
  if (b) {
    r := 1;
  } else {
    r := 0;
  }
};
#end

-- The body lowers to a single ite.
#guard match lookupProc pIfs "withIf" with
       | some d =>
         match d.body with
         | [.ite _ _ _ _] => true
         | _ => false
       | none => false


private def pIfNoElse : Strata.Program :=
#strata
program CoreMatch;

procedure withIfNoElse(b : bool, out r: int)
{
  r := 0;
  if (b) {
    r := 1;
  }
};
#end

-- if-without-else lowers to ite with an empty else block.
#guard match lookupProc pIfNoElse "withIfNoElse" with
       | some d =>
         match d.body with
         | [_, .ite _ _ [] _] => true
         | _ => false
       | none => false


private def pBlock : Strata.Program :=
#strata
program CoreMatch;

procedure withBlock(out r: int)
{
  lbl: {
    r := 1;
  }
};
#end

-- A labelled block statement lowers to `Stmt.block "lbl" [...]`.
#guard match lookupProc pBlock "withBlock" with
       | some d =>
         d.body.any fun
           | .block lbl _ _ => lbl == "lbl"
           | _ => false
       | none => false


/-! Statement-arm accessor inits

`buildArmInits` prepends `var b : T := D..f(scrut);` to each arm
body that binds pattern variables.  Verify the lowered procedure
references the accessor op. -/

private def pAccessor : Strata.Program :=
#strata
program CoreMatch;

datatype OptInt () { None(), Some(val : int) };

procedure unwrapOr(o : OptInt, dflt : int, out r: int)
{
  match o {
    None()             => { r := dflt; }
    Some(val : int)    => { r := val; }
  }
};
#end

-- The Some arm's body should contain an accessor call to `OptInt..val`.
#guard match lookupProc pAccessor "unwrapOr" with
       | some d => d.body.any (stmtHasOp · "OptInt..val")
       | none => false

-- The same procedure also threads testers `OptInt..isNone` and
-- `OptInt..isSome` through the ite chain.
#guard match lookupProc pAccessor "unwrapOr" with
       | some d => d.body.any (stmtHasOp · "OptInt..isNone")
       | none => false


/-! Procedure spec translation -/

private def pSpec : Strata.Program :=
#strata
program CoreMatch;

procedure clamp(x : int, out r: int)
spec {
  requires x >= 0;
  ensures r >= 0;
  ensures r <= 100;
}
{
  r := 0;
};
#end

#guard match lookupProc pSpec "clamp" with
       | some d => d.spec.preconditions.length == 1
       | none => false

#guard match lookupProc pSpec "clamp" with
       | some d => d.spec.postconditions.length == 2
       | none => false

-- Default attribute on a non-`free` clause.
#guard match lookupProc pSpec "clamp" with
       | some d =>
         match d.spec.preconditions with
         | [(_, check)] => check.attr == .Default
         | _ => false
       | none => false


private def pSpecFree : Strata.Program :=
#strata
program CoreMatch;

procedure usingFree(x : int, out r: int)
spec {
  free requires x >= 0;
  free ensures r == x;
}
{
  r := x;
};
#end

-- `requires free` produces `CheckAttr.Free`.
#guard match lookupProc pSpecFree "usingFree" with
       | some d =>
         match d.spec.preconditions with
         | [(_, check)] => check.attr == .Free
         | _ => false
       | none => false

#guard match lookupProc pSpecFree "usingFree" with
       | some d =>
         match d.spec.postconditions with
         | [(_, check)] => check.attr == .Free
         | _ => false
       | none => false


private def pSpecLabel : Strata.Program :=
#strata
program CoreMatch;

procedure named(out r : int)
spec {
  ensures [outNonNeg]: r >= 0;
}
{
  r := 0;
};
#end

-- User-provided label is used verbatim.
#guard match lookupProc pSpecLabel "named" with
       | some d =>
         match d.spec.postconditions with
         | [(lbl, _)] => lbl == "outNonNeg"
         | _ => false
       | none => false


/-! Type translation breadth

Procedures whose parameters and bodies exercise type forms beyond
the int/bool/datatype set the rest of the suite covers. -/

private def pTypeBreadth : Strata.Program :=
#strata
program CoreMatch;

procedure typeBreadth(
    a : bv8, b : bv32, s : string, x : real,
    m : Map int bool, q : Sequence int,
    out r : int)
{
  r := 0;
};
#end

-- Just confirm the procedure parses and lowers without error.
#guard match lookupProc pTypeBreadth "typeBreadth" with
       | some _ => true
       | none => false

-- The header carries every binding the procedure declares (including
-- the outparam): six inputs + one outparam = seven entries.
#guard match lookupProc pTypeBreadth "typeBreadth" with
       | some d => d.header.inputs.length == 7
       | none => false


private def pBitvecs : Strata.Program :=
#strata
program CoreMatch;

procedure bitvecs(a : bv1, b : bv16, c : bv64, out r : int)
{
  r := 0;
};
#end

#guard match lookupProc pBitvecs "bitvecs" with
       | some d => d.header.inputs.length == 4
       | none => false


private def pNestedTypes : Strata.Program :=
#strata
program CoreMatch;

procedure nestedTypes(
    sm : Sequence (Map int bool),
    ms : Map string (Sequence real),
    out r : int)
{
  r := 0;
};
#end

#guard match lookupProc pNestedTypes "nestedTypes" with
       | some d => d.header.inputs.length == 3
       | none => false


/-! Empty / minimal programs

The translator should accept a program with no declarations, and a
program with only a datatype. -/

private def pEmpty : Strata.Program :=
#strata
program CoreMatch;
#end

#guard match parseToCore pEmpty with
       | .ok p => p.decls.isEmpty
       | .error _ => false


private def pOnlyDatatype : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };
#end

#guard match parseToCore pOnlyDatatype with
       | .ok p => !p.decls.isEmpty   -- at least the datatype decl
       | .error _ => false


/-! Bare `var n : T;` (varStatement)

`toMStmt`'s `varStatement` branch returns `[]` — the variable is
introduced into the bvar stack only; no Core statement is emitted. -/

private def pBareVar : Strata.Program :=
#strata
program CoreMatch;

procedure bareVar(out r : int)
{
  var x : int;
  r := 0;
};
#end

-- Body should have just the assignment, no init for `x`.
#guard match lookupProc pBareVar "bareVar" with
       | some d => d.body.length == 1
       | none => false


/-! Non-deterministic `if (*)`

`toCoreCondBool`'s `.condNondet` branch lowers to
`Imperative.ExprOrNondet.nondet`. -/

private def pNondetIf : Strata.Program :=
#strata
program CoreMatch;

procedure nondetIf(out r : int)
{
  if * {
    r := 1;
  } else {
    r := 0;
  }
};
#end

#guard match lookupProc pNondetIf "nondetIf" with
       | some d =>
         match d.body with
         | [.ite .nondet _ _ _] => true
         | _ => false
       | none => false


/-! Multiple datatypes in one block declaration

`command_datatypes` accepts a comma-separated list of datatype decls
in one statement; the cache is populated for all of them and the
emitted `MDecl.type (.data lds)` carries every datatype. -/

private def pMultiDatatypes : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };

datatype Shape () { Circle(radius : int), Square(side : int) };

function dispatch(c : Color, s : Shape) : int
{
  match c {
    arm Red()   =>
      match s {
        arm Circle(radius : int) => radius;
        arm Square(side : int)   => side;
      };
    arm Green() => 0;
    arm Blue()  => 0;
  }
};
#end

-- Both datatypes are usable from the same function — confirms the
-- cache survives across decls.
#guard match parseToCore pMultiDatatypes with
       | .ok _    => true
       | .error _ => false


/-! Custom labels on assert/assume

A user-supplied label is preserved in the lowered Core statement. -/

private def pLabels : Strata.Program :=
#strata
program CoreMatch;

procedure withLabels(b : bool, out r : int)
{
  assert [precond]: b;
  assume [postcond]: b;
  r := 0;
};
#end

#guard match lookupProc pLabels "withLabels" with
       | some d =>
         d.body.any fun
           | .assert lbl _ _ => lbl == "precond"
           | _ => false
       | none => false

#guard match lookupProc pLabels "withLabels" with
       | some d =>
         d.body.any fun
           | .assume lbl _ _ => lbl == "postcond"
           | _ => false
       | none => false


/-! Synthesised labels for unlabelled assertions

`freshLabel` synthesises labels of the form `prefix_N_pos` when the
user doesn't provide one.  We confirm the produced label is non-empty
and starts with the right prefix. -/

private def pUnlabelled : Strata.Program :=
#strata
program CoreMatch;

procedure unlabelled(b : bool, out r : int)
{
  assert b;
  assume b;
  r := 0;
};
#end

#guard match lookupProc pUnlabelled "unlabelled" with
       | some d =>
         d.body.any fun
           | .assert lbl _ _ => !lbl.isEmpty && lbl.startsWith "assert"
           | _ => false
       | none => false

#guard match lookupProc pUnlabelled "unlabelled" with
       | some d =>
         d.body.any fun
           | .assume lbl _ _ => !lbl.isEmpty && lbl.startsWith "assume"
           | _ => false
       | none => false


end CoreMatchStatementsAndSpecsTest
