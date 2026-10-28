/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import Strata.Backends.CBMC.CollectSymbols
meta import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.DDMTransform.Translate

/-! # `emitProc` hoisting: which functions get GOTO bodies

End-to-end from DDM-parsed Core programs through `emitProc` with
`topLevelFuncs`. A function whose applications are all hoistable gets a real
GOTO body; a function with an application that hoisting must leave in place —
under a quantifier, in a loop invariant, or in a procedure contract — stays
an uninterpreted `mathematical_function` everywhere, so no remaining
`function_application` refers to a code-typed symbol. Recursive functions
get a body only with `hoistRecursive`. -/

meta section

open Strata

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Run `emitProc` on the program's first procedure with all top-level
    functions eligible; return the symbol table and GOTO function names. -/
private def emitHoisted (p : StrataDDM.Program) (hoistRecursive : Bool := false) :
    IO (Lean.Json × List String) := do
  let (tcPgm, Env) ← IO.ofExcept (typeCheckCore (translateCore p))
  let some proc := tcPgm.decls.findSome? (·.getProc?)
    | throw (IO.userError "no procedure")
  let axioms := tcPgm.decls.filterMap (·.getAxiom?)
  let ctx ← IO.ofExcept (procedureToGotoCtx Env proc (axioms := axioms))
  let extraSyms ← IO.ofExcept (collectExtraSymbols tcPgm)
  let funcs := tcPgm.decls.flatMap fun d => match d with
    | .func f _ => [f]
    | .recFuncBlock fs _ => fs
    | _ => []
  let pname := Core.CoreIdent.toPretty proc.header.name
  let (symtab, goto) ← emitProc pname ctx (Lean.toJson extraSyms) (moduleName := "test")
    (topLevelFuncs := funcs) (Env := Env) (hoistRecursive := hoistRecursive)
  let names := match goto.getObjValD "functions" with
    | .arr fns => fns.toList.filterMap fun f => (f.getObjValD "name").getStr?.toOption
    | _ => []
  return (symtab, names)

/-- The `id` of a symbol's type in the (wrapped) symbol table. -/
private def symTypeId (symtab : Lean.Json) (name : String) : String :=
  let sym := (symtab.getObjValD "symbolTable").getObjValD name
  ((sym.getObjValD "type").getObjValD "id").getStr?.toOption.getD ""

-------------------------------------------------------------------------------

-- Baseline: a direct call is hoisted, so `f` gets a GOTO body.
def DirectCall :=
#strata
program Core;
function f(x : int) : int { x }
procedure test(y : int) {
  assert (f(y) == y);
};
#end

/-- info: (["test", "f"], "code") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted DirectCall
  return (names, symTypeId symtab "f")

-- Quantifier: `f(q)` mentions the bound variable, so `f` stays
-- uninterpreted, including at the direct call outside the quantifier.
def QuantifiedCall :=
#strata
program Core;
function f(x : int) : int { x }
procedure test(y : int) {
  assert (f(y) == y);
  assert (forall q : int :: f(q) == q);
};
#end

/-- info: (["test"], "mathematical_function") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted QuantifiedCall
  return (names, symTypeId symtab "f")

-- Contract: `f` appears in a precondition, so it stays uninterpreted.
def ContractCall :=
#strata
program Core;
function f(x : int) : int { x }
procedure test(y : int)
spec {
  requires (f(y) == y);
} {
  assert (f(y) == y);
};
#end

/-- info: (["test"], "mathematical_function") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted ContractCall
  return (names, symTypeId symtab "f")

-- Loop invariant: `f` appears in a `#spec_loop_invariant` annotation, so it
-- stays uninterpreted even though the loop body also calls it.
def InvariantCall :=
#strata
program Core;
function f(x : int) : int { x }
procedure test(n : int) {
  var i : int := 0;
  while (int.lt(i, n))
    invariant int.ge(f(i), 0)
  {
    i := f(int.add(i, 1));
  }
};
#end

/-- info: (["test"], "mathematical_function") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted InvariantCall
  return (names, symTypeId symtab "f")

-- Only the function used under the quantifier is excluded: `g` is still
-- given a body.
def MixedCalls :=
#strata
program Core;
function f(x : int) : int { x }
function g(x : int) : int { x }
procedure test(y : int) {
  assert (g(y) == y);
  assert (forall q : int :: f(q) == q);
};
#end

/-- info: (["test", "g"], "mathematical_function", "code") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted MixedCalls
  return (names, symTypeId symtab "f", symTypeId symtab "g")

-- Recursion: `fact` calls itself, so by default it stays uninterpreted. Its
-- non-recursive caller `twice` still gets a body. With `hoistRecursive`,
-- `fact` gets a body too.
def RecursiveCall :=
#strata
program Core;
rec function fact (n : int) : int
{
  if int.le(n, 1) then 1 else int.mul(n, fact(int.sub(n, 1)))
};
function twice(x : int) : int { int.add(fact(x), fact(x)) }
procedure test(y : int) {
  assert (twice(y) == int.mul(2, fact(y)));
};
#end

/-- info: (["test", "twice"], "mathematical_function", "code") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted RecursiveCall
  return (names, symTypeId symtab "fact", symTypeId symtab "twice")

/-- info: (["test", "twice", "fact"], "code", "code") -/
#guard_msgs in
#eval do
  let (symtab, names) ← emitHoisted RecursiveCall (hoistRecursive := true)
  return (names, symTypeId symtab "fact", symTypeId symtab "twice")

end
