/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # A loop body is a scope, and so is a top-level block

Every variable reference in a translated program names the variable the source
names at that position. For a loop that means the guard, the invariant, the
measure and the statements after the loop are resolved in the scope enclosing the
loop, while the body's own statements additionally see what the body declares. A
top-level `{ ... }` command is the same one level up: its declarations are visible
within it and nowhere after it.

These tests read the names back off the translated AST. Lambda is locally
nameless, so a free variable carries its own name, and `getFvars` /
`HasVarsImp.readVars` report the names the AST holds independently of how it
would be printed. `RoundtripTest` covers the printing direction. See P505711117.
-/

namespace Strata.Test.LoopBodyScope

open Strata
open Strata.CoreDDM
open Lambda Imperative

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Variable names, in the order the AST holds them. -/
private def names (vs : List Core.Expression.Ident) : List String := vs.map (·.name)

/-- The structured statements of procedure `name`. -/
private def procStmts (prog : Core.Program) (name : String) : Core.Statements :=
  match prog.findProcByString? name with
  | some proc => proc.body.getStructured.toOption.getD []
  | none => []

/-- The statements following the first loop, at the loop's own nesting level. -/
private def afterLoop : Core.Statements → Core.Statements
  | [] => []
  | .loop .. :: rest => rest
  | _ :: rest => afterLoop rest

/-- The names read at each position around the first loop of procedure `p`: its
    guard, invariant and measure, then those read inside the body, then those read
    by the statements following the loop. `readVars` is the whole-statement read
    set, so `body` and `after` include nested statements. -/
private def loopReport (prog : StrataDDM.Program) : String :=
  let ss := procStmts (translateCore prog) "p"
  match ss.findSome? (fun s =>
      match s with
      | .loop guard measure invs body _ => some (guard, measure, invs, body)
      | _ => none) with
  | none => "no loop found"
  | some (guard, measure, invs, body) =>
    let invNames := names (invs.flatMap fun i => HasFvars.getFvars i.2)
    let measureNames := names ((measure.map HasFvars.getFvars).getD [])
    let bodyNames := names (body.flatMap HasVarsImp.readVars)
    let afterNames := names ((afterLoop ss).flatMap HasVarsImp.readVars)
    s!"guard {names guard.getVars}, invariant {invNames}, measure {measureNames}, \
       body {bodyNames}, after {afterNames}"

/-! ## A body declaration is visible in the body and nowhere else

`dead` is deliberately unused, so it should appear at no position below. -/

private def oneDecl :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  decreases int.sub(n, i)
  invariant int.le(0, i)
  {
    var dead : int := 5;
    i := int.add(i, 1);
  }
  if (int.lt(i, n)) {
    i := int.add(i, 100);
  }
  i := int.add(i, 200);
};
#end

/-- info: guard [i, n], invariant [i], measure [n, i], body [i], after [i, n, i, i] -/
#guard_msgs in
#eval IO.println (loopReport oneDecl)

/-! ## Two declarations in the body

The same names are read at the same positions with two declarations rather than
one, so the result does not depend on how many names the body introduces. -/

private def twoDecls :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var d1 : int := 5;
    var d2 : int := 7;
    i := int.add(i, 1);
  }
  i := int.add(i, 100);
};
#end

/-- info: guard [i, n], invariant [], measure [], body [i], after [i] -/
#guard_msgs in
#eval IO.println (loopReport twoDecls)

/-! ## A nondeterministic guard

`while *` reads nothing, so the guard names no variable while the statements
after the loop still name what the source wrote. -/

private def nondetGuard :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while *
  {
    var dead : int := 5;
    i := int.add(i, 1);
  }
  i := int.add(i, 100);
};
#end

/-- info: guard [], invariant [], measure [], body [i], after [i] -/
#guard_msgs in
#eval IO.println (loopReport nondetGuard)

/-! ## A body that declares nothing

The baseline: with no declaration in the body, every position names exactly what
the source wrote. -/

private def noDecls :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    i := int.add(i, 1);
  }
  i := int.add(i, 100);
};
#end

/-- info: guard [i, n], invariant [], measure [], body [i], after [i] -/
#guard_msgs in
#eval IO.println (loopReport noDecls)

/-! ## A declaration before the loop is visible inside the body

`before` is in scope at the loop, so the body reads it by name, alongside `i`. -/

private def declBeforeLoop :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  var before : int := 5;
  while (int.lt(i, n))
  {
    i := int.add(i, before);
  }
  i := int.add(i, 100);
};
#end

/-- info: guard [i, n], invariant [], measure [], body [i, before], after [i] -/
#guard_msgs in
#eval IO.println (loopReport declBeforeLoop)

/-! ## A loop nested in a body that declares

The inner loop's guard is resolved in the outer body's scope, so it names `i` and
the outer body's `outerDecl`. The statement after the inner loop, still inside the
outer body, names the same two. -/

private def nestedLoops :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var outerDecl : int := 5;
    while (int.lt(i, outerDecl))
    {
      var innerDecl : int := 7;
      i := int.add(i, 1);
    }
    i := int.add(i, outerDecl);
  }
};
#end

/-- The names read at each position around the loop nested in the outer body. -/
private def innerLoopReport (prog : StrataDDM.Program) : String :=
  let outerBody := (procStmts (translateCore prog) "p").findSome? fun s =>
    match s with
    | .loop _ _ _ body _ => some body
    | _ => none
  match outerBody with
  | none => "no loop found"
  | some body =>
    match body.findSome? (fun s =>
        match s with
        | .loop guard _ _ inner _ => some (guard, inner)
        | _ => none) with
    | none => "no nested loop found"
    | some (guard, inner) =>
      s!"inner guard {names guard.getVars}, \
         inner body {names (inner.flatMap HasVarsImp.readVars)}, \
         after {names ((afterLoop body).flatMap HasVarsImp.readVars)}"

/-- info: inner guard [i, outerDecl], inner body [i], after [i, outerDecl] -/
#guard_msgs in
#eval IO.println (innerLoopReport nestedLoops)

/-! ## A top-level block

`b` is declared after the block, so its value names `a`, the constant declared
before it. `blockLocal` is visible only within the block.

A `const` reference is an operator rather than a free variable, so this reads the
expression the AST holds rather than its variables. `RoundtripTest` has no
counterpart: a top-level block prints with an empty procedure name, which does not
parse back. -/

private def blockCommandThenConst :=
#strata
program Core;
const a : int := 1;
{
  var blockLocal : int := 5;
};
const b : int := int.add(a, 2);
#end

/-- The value of the nullary function a `const` declaration becomes. -/
private def constValue (prog : Core.Program) (name : String) : String :=
  match Core.Program.Function.find? prog ⟨name, ()⟩ with
  | some f => match f.body with
    | some e => (Std.format e).pretty
    | none => "no value"
  | none => "no such declaration"

/-- info: int.add(a, 2) -/
#guard_msgs in
#eval IO.println (constValue (translateCore blockCommandThenConst) "b")

end Strata.Test.LoopBodyScope

end
