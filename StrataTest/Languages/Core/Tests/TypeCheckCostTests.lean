/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementType

meta section

/-! ## Type-checking cost

Each check compares two amounts of type-checking work, counted in heartbeats (allocations),
which are deterministic. -/

namespace Core.TypeCheckCostTests

open Lambda Imperative

/-- The type `int`. -/
def intTy : Expression.Ty := .forAll [] (.tcons "int" [])
/-- The type `bool`. -/
def boolTy : Expression.Ty := .forAll [] (.tcons "bool" [])
/-- The integer literal `i`. -/
def ic (i : Nat) : Expression.Expr := .intConst Core.coreLoc (Int.ofNat i)
/-- The variable `n`, unannotated. -/
def fv (n : String) : Expression.Expr := .fvar Core.coreLoc (n : Expression.Ident) none

/-- A context binding `x : int`, `c : bool` and `vars` further `bool` variables. -/
def envWith (vars : Nat) : TEnv Unit :=
  TEnv.default.updateContext
    { types := Strata.Util.HMaps.ofScopes
        [(("x" : Expression.Ident), intTy) :: (("c" : Expression.Ident), boolTy) ::
          (List.range vars).map fun i => ((s!"v_{i}" : Expression.Ident), boolTy)] }

/-- Heartbeats spent type checking `ss` in `Env`; fails if checking fails. -/
def checkCost (Env : TEnv Unit) (ss : List Statement) : IO Nat := do
  let h0 ← IO.getNumHeartbeats
  let ok ← IO.lazyPure fun _ =>
    (Statement.typeCheck LContext.default Env Program.init none ss).isOk
  let h1 ← IO.getNumHeartbeats
  unless ok do throw (IO.userError "type checking failed")
  return h1 - h0

/-- Heartbeats spent checking the guard `c` of an `if` with `arm` as both branches: the cost with
    the guard minus the cost with a nondeterministic guard. -/
def guardCost (Env : TEnv Unit) (arm : List Statement) : IO Int := do
  let det := [Stmt.ite (.det (fv "c")) arm arm .empty]
  let nondet := [Stmt.ite .nondet arm arm .empty]
  let _ ← checkCost Env det
  let _ ← checkCost Env nondet
  return (← checkCost Env det : Int) - (← checkCost Env nondet : Int)

/-- `k` assignments `x := i`. -/
def assigns (k : Nat) : List Statement :=
  (List.range k).map fun i => Statement.set "x" (ic i) .empty

/-- `k` declarations `var y_i : int := i`. -/
def decls (k : Nat) : List Statement :=
  (List.range k).map fun i =>
    Statement.init (s!"y_{i}" : Expression.Ident) intTy (.det (ic i)) .empty

/-- Checking the guard of an `if` whose branches are `n` assignments each costs less than a tenth
    of checking the branches. -/
def guardSmallNextToArms (n : Nat) : IO Bool := do
  let guard ← guardCost (envWith 0) (assigns n)
  let arms ← checkCost (envWith 0) [Stmt.ite .nondet (assigns n) (assigns n) .empty]
  return 10 * guard < arms

/-- The cost of checking an `if` guard does not grow with the number of variables in scope. -/
def guardIgnoresScopeSize (n : Nat) : IO Bool := do
  let small ← guardCost (envWith n) (assigns 1)
  let large ← guardCost (envWith (4 * n)) (assigns 1)
  return large < 2 * small

/-- The cost of checking the statements `gen k` grows linearly with `k`. -/
def costLinear (gen : Nat → List Statement) (n : Nat) : IO Bool := do
  let _ ← checkCost (envWith 0) (gen n)
  let small ← checkCost (envWith 0) (gen n)
  let large ← checkCost (envWith 0) (gen (4 * n))
  return large < 6 * small

/-- `if * then x := 0 else …`, nested `k` deep in the else branches. -/
def elseIfChain : Nat → Statement
  | 0 => .ite .nondet (assigns 1) [] .empty
  | k + 1 => .ite .nondet (assigns 1) [elseIfChain k] .empty

/-- `if c then { x := 0; … }`, nested `k` deep in the then branches. -/
def thenChain : Nat → Statement
  | 0 => .ite (.det (fv "c")) (assigns 1) [] .empty
  | k + 1 => .ite (.det (fv "c")) (assigns 1 ++ [thenChain k]) [] .empty

/-- `if * then { var y_0 : int := 0; x := y_0 } else …`, nested `k` deep in the else branches. -/
def localChain (k : Nat) : Statement :=
  .ite .nondet (decls 1 ++ [Statement.set "x" (fv "y_0") .empty])
    (match k with
      | 0 => []
      | k + 1 => [localChain k])
    .empty

/-- info: The guard costs under a tenth of 200-assignment branches: true -/
#guard_msgs in
#eval do IO.println s!"The guard costs under a tenth of 200-assignment branches: {←
  guardSmallNextToArms 200}"

/-- info: Guard cost is independent of scope size (100 against 400 variables): true -/
#guard_msgs in
#eval do IO.println s!"Guard cost is independent of scope size (100 against 400 variables): {←
  guardIgnoresScopeSize 100}"

/-- info: Cost is linear in the number of declarations: true -/
#guard_msgs in
#eval do IO.println s!"Cost is linear in the number of declarations: {← costLinear decls 100}"

/-- info: Cost is linear in the depth of else-if chains: true -/
#guard_msgs in
#eval do IO.println s!"Cost is linear in the depth of else-if chains: {←
  costLinear (fun k => [elseIfChain k]) 50}"

/-- info: Cost is linear in the depth of nested then branches: true -/
#guard_msgs in
#eval do IO.println s!"Cost is linear in the depth of nested then branches: {←
  costLinear (fun k => [thenChain k]) 50}"

/-- info: Cost is linear in the depth of nested local declarations: true -/
#guard_msgs in
#eval do IO.println s!"Cost is linear in the depth of nested local declarations: {←
  costLinear (fun k => [localChain k]) 50}"

end Core.TypeCheckCostTests
