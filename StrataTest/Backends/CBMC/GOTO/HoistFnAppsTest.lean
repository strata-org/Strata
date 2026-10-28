/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Backends.CBMC.GOTO.HoistFnApps

/-! # `hoistProgram` unit tests

Pin the hoisting rewrite on hand-built GOTO programs, independent of the
Core→GOTO translation and of CBMC:

1. a defined-function application in a straight-line instruction becomes a
   `DECL`/`FUNCTION_CALL` pair before the host, with nested applications
   called in dependency order and undefined callees left in place;
2. structurally identical applications within one instruction share a single
   call (the pure-function memo);
3. an application inside an `ite` branch is guarded by instruction-level
   branching, never executed unconditionally;
4. a short-circuit operator with an application in its non-first operand is
   desugared and guarded the same way;
5. the location renumbering keeps a `GOTO` pointing at the first hoisted
   instruction of its original target;
6. applications inside quantifier bodies are never hoisted;
7. `residualFnApps` / `jsonFnAppNames` report the applications hoisting
   leaves in place (quantifier bodies, spec annotations, contracts). -/

meta section

namespace CProverGOTO.HoistFnAppsTest

open CProverGOTO

private def intTy : Ty := .Integer

private def x : Expr := Expr.symbol "main::1::x" intTy

private def app (f : String) (args : List Expr) (ty : Ty := intTy) : Expr :=
  { id := .functionApplication f, type := ty, operands := args }

private def mkInst (ty : InstructionType) (code : Code) (loc : Nat)
    (guard : Expr := .true) (target : Option Nat := none) : Instruction :=
  { type := ty, code := code, locationNum := loc, guard := guard, target := target }

private def assertInst (c : Expr) (loc : Nat) : Instruction :=
  mkInst .ASSERT (Code.assert c) loc

private def runHoist (defined : List String) (insts : List Instruction) :
    Program × List (String × Ty) :=
  hoistProgram (Std.HashSet.ofList defined) "main" { instructions := insts.toArray }

/-- Instruction types, in order, as a compact trace. -/
private def trace (p : Program) : List InstructionType :=
  p.instructions.toList.map (·.type)

/-- Callee names of `FUNCTION_CALL` instructions, in order. -/
private def callees (p : Program) : List String :=
  p.instructions.toList.filterMap fun inst =>
    match inst.type, inst.code.operands with
    | .FUNCTION_CALL, [_, callee, _] =>
      match callee.id with
      | .nullary (.symbol n) => some n
      | _ => none
    | _, _ => none

/-- Does any expression in the program still contain an application of `f`? -/
private partial def mentionsApp (f : String) (e : Expr) : Bool :=
  (match e.id with | .functionApplication n => n == f | _ => false)
  || e.operands.any (mentionsApp f)

-- 1. Nested applications: `f(g(x))` hoists `g` then `f`, and an undefined
--    callee `h` stays in place as an application.
private def nested := runHoist ["f", "g"]
  [assertInst (app "h" [app "f" [app "g" [x]]] (ty := .Boolean)) 0]

#guard trace nested.1 == [.DECL, .FUNCTION_CALL, .DECL, .FUNCTION_CALL, .ASSERT]
#guard callees nested.1 == ["g", "f"]
#guard nested.2.length == 2
-- `h` is not in `defined`, so it survives as an application in the host.
#guard mentionsApp "h" (nested.1.instructions.back!.code.operands.head!)
-- `f`/`g` no longer appear as applications anywhere.
#guard !(nested.1.instructions.any fun i => i.code.operands.any (mentionsApp "f"))

-- 2. Memo: two structurally identical applications issue one call.
private def dup := runHoist ["f"]
  [assertInst { id := .binary .Equal, type := .Boolean,
                operands := [app "f" [x], app "f" [x]] } 0]

#guard callees dup.1 == ["f"]
#guard dup.2.length == 1

-- Different arguments are different applications: two calls.
private def dup2 := runHoist ["f"]
  [assertInst { id := .binary .Equal, type := .Boolean,
                operands := [app "f" [x], app "f" [Expr.constant "1" intTy]] } 0]

#guard callees dup2.1 == ["f", "f"]

-- 3. `ite` guarding: the call in the else branch is reached only through a
--    conditional GOTO, and the ite node is replaced by a temporary.
private def guarded := runHoist ["rec"]
  [assertInst { id := .binary .Equal, type := .Boolean,
                operands := [{ id := .ternary .ite, type := intTy,
                               operands := [Expr.constant "true" .Boolean,
                                            Expr.constant "1" intTy,
                                            app "rec" [x]] },
                             Expr.constant "1" intTy] } 0]

-- DECL tmp; GOTO else; ASSIGN tmp := 1; GOTO end; DECL c; CALL rec; ASSIGN tmp := c; ASSERT
#guard trace guarded.1 ==
  [.DECL, .GOTO, .ASSIGN, .GOTO, .DECL, .FUNCTION_CALL, .ASSIGN, .ASSERT]
-- The guarded GOTO (index 1) jumps to the else branch (index 4), the
-- unconditional GOTO (index 3) jumps past it to the host (index 7).
#guard guarded.1.instructions[1]!.target == some 4
#guard guarded.1.instructions[3]!.target == some 7
-- Memo scoping: a temp bound in a branch is not reused after the join — the
-- host's second `rec(x)` (outside the ite) gets its own call.
private def branchScoped := runHoist ["rec"]
  [assertInst { id := .binary .Equal, type := .Boolean,
                operands := [{ id := .ternary .ite, type := intTy,
                               operands := [Expr.constant "true" .Boolean,
                                            Expr.constant "1" intTy,
                                            app "rec" [x]] },
                             app "rec" [x]] } 0]

#guard callees branchScoped.1 == ["rec", "rec"]

-- 4. Short-circuit desugaring: `c || rec(x)` guards the call like an ite.
private def shortCircuit := runHoist ["rec"]
  [assertInst { id := .multiary .Or, type := .Boolean,
                operands := [Expr.constant "false" .Boolean, app "rec" [x] (ty := .Boolean)] } 0]

-- Same shape as the explicit `ite` case: `false || rec(x)` desugars to
-- `ite false true rec(x)`, so the then-branch assigns `true` and only the
-- else-branch calls `rec`.
#guard trace shortCircuit.1 ==
  [.DECL, .GOTO, .ASSIGN, .GOTO, .DECL, .FUNCTION_CALL, .ASSIGN, .ASSERT]
#guard shortCircuit.1.instructions[1]!.target == some 4
#guard shortCircuit.1.instructions[3]!.target == some 7
#guard callees shortCircuit.1 == ["rec"]

-- A call-free `||` keeps its plain expression form (no lowering).
private def plainOr := runHoist ["rec"]
  [assertInst { id := .multiary .Or, type := .Boolean,
                operands := [Expr.constant "false" .Boolean, x] } 0]

#guard trace plainOr.1 == [.ASSERT]

-- 5. GOTO target patching: a jump to instruction 1 lands on the first
--    instruction hoisted for it, so the jumped-to code still runs its call.
private def jump := runHoist ["f"]
  [mkInst .GOTO Code.skip 0 (target := some 1),
   assertInst { id := .binary .Equal, type := .Boolean,
                operands := [app "f" [x], Expr.constant "0" intTy] } 1]

#guard trace jump.1 == [.GOTO, .DECL, .FUNCTION_CALL, .ASSERT]
#guard jump.1.instructions[0]!.target == some 1
-- Locations are renumbered densely.
#guard jump.1.instructions.toList.map (·.locationNum) == [0, 1, 2, 3]

-- 6. Quantifiers: an application of a defined function inside a quantifier
--    body mentions the bound variable, so it must not be hoisted (it would
--    otherwise be evaluated at a free `__quant_var_0`).
private def qv : Expr := Expr.symbol "__quant_var_0" intTy

private def quantBody : Expr :=
  { id := .binary .Equal, type := .Boolean,
    operands := [app "f" [qv], Expr.constant "0" intTy] }

private def forallF : Expr :=
  { id := .binary .Forall, type := .Boolean, operands := [qv, quantBody] }

private def quant := runHoist ["f"] [assertInst forallF 0]

#guard trace quant.1 == [.ASSERT]
#guard quant.2.isEmpty
#guard mentionsApp "f" (quant.1.instructions[0]!.code.operands.head!)
-- A quantifier does not count as a hoistable call, so an enclosing `ite`
-- or short-circuit operator is not lowered on its account.
#guard !exprHasHoistableCall (Std.HashSet.ofList ["f"]) forallF
private def quantOr := runHoist ["f"]
  [assertInst { id := .multiary .Or, type := .Boolean,
                operands := [Expr.constant "false" .Boolean, forallF] } 0]
#guard trace quantOr.1 == [.ASSERT]
-- A call outside the quantifier in the same instruction is still hoisted.
private def quantMixed := runHoist ["f"]
  [assertInst { id := .multiary .And, type := .Boolean,
                operands := [{ id := .binary .Equal, type := .Boolean,
                               operands := [app "f" [x], Expr.constant "0" intTy] },
                             forallF] } 0]
#guard callees quantMixed.1 == ["f"]
#guard mentionsApp "f" (quantMixed.1.instructions.back!.code.operands.head!)

-- 7. Residual applications: `residualFnApps` reports exactly the applications
--    hoisting leaves in place — under quantifiers and in `namedFields` (spec
--    annotations) — so `emitProc` can keep those callees uninterpreted.
private def withSpec : Expr :=
  (app "g" [x] (ty := .Boolean)).setNamedField "#spec_loop_invariant"
    (app "inv" [x] (ty := .Boolean))

#guard residualFnApps { instructions := #[assertInst forallF 0] } == ["f"]
#guard residualFnApps { instructions := #[assertInst withSpec 0] } == ["inv"]
-- Hoistable applications are not residual.
#guard residualFnApps { instructions := #[assertInst (app "f" [x] (ty := .Boolean)) 0] } == []

-- Contracts are stored as serialized JSON; their callees are found there.
#guard (match exprToJson (app "pre" [x] (ty := .Boolean)) with
        | .ok j => jsonFnAppNames j
        | .error _ => []) == ["pre"]

end CProverGOTO.HoistFnAppsTest

end
