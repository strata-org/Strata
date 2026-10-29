/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.GOTO.Semantics
import Strata.Languages.GOTO.SemanticsEval
import Strata.Languages.GOTO.SemanticsProps

/-!
# Tests for GOTO Semantics

Basic sanity checks that the semantics rules can be instantiated and
that the simple properties hold.
-/

open CProverGOTO CProverGOTO.Semantics

/-! ## Test helpers -/

/-- A trivial expression evaluator that handles constants and symbols. -/
def testEval : ExprEval
  | σ, e => match e.id with
    | .nullary (.constant "true") => some (.bool true)
    | .nullary (.constant "false") => some (.bool false)
    | .nullary (.constant v) => v.toInt?.map .int
    | .nullary (.symbol name) => σ name
    | _ => none

/-- A no-call relation (no function calls succeed). -/
def noCall : CallResultRel := fun _ _ _ _ _ _ => False

/-! ## Simple program: SKIP; END_FUNCTION -/

def skipProg : Program :=
  { name := "test"
    instructions := #[
      { type := .SKIP, locationNum := 0 },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example : ExecProg noCall testEval (fun _ => none) skipProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.skip rfl
  · exact ExecProg.end_function rfl

/-! ## ASSERT pass -/

def assertPassProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSERT, locationNum := 0,
        guard := Expr.constant "true" .Boolean },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example : ExecProg noCall testEval (fun _ => none) assertPassProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.assert_pass rfl rfl
  · exact ExecProg.end_function rfl

/-! ## ASSERT fail still advances -/

def assertFailProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSERT, locationNum := 0,
        guard := Expr.constant "false" .Boolean,
        sourceLoc := { SourceLocation.nil with comment := "test assertion" } },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- Assertion failure still allows execution to continue
example : ExecProg noCall testEval (fun _ => none) assertFailProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.assert_fail rfl rfl
  · exact ExecProg.end_function rfl

-- But the program is NOT safe
example : ¬ ProgramSafe noCall testEval (fun _ => none) assertFailProg Store.empty := by
  intro hsafe
  apply hsafe 0 Store.empty
  · exact Reachable.refl
  · exact ⟨rfl, rfl⟩

/-! ## Reachability transitivity -/

example {cr : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {σ : Store} :
    Reachable cr eval fenv prog 0 σ 0 σ := Reachable.refl

/-! ## Regression: `Reachable` steps past `SET_RETURN_VALUE`

`StepInstr` has NO rule for `SET_RETURN_VALUE` (it is handled only at the
`ExecProg` level). Because `Reachable` used to be the reflexive-transitive
closure of `StepInstr` alone, reachability got STUCK at a `SET_RETURN_VALUE`
instruction: no state past it was reachable. Consequently `ProgramSafe`, which
quantifies over reachable states, held VACUOUSLY for any assertion following a
`SET_RETURN_VALUE` — a false "safe" for a genuinely violable assertion.

The new `Reachable.step_set_return_value` constructor advances the PC past a
`SET_RETURN_VALUE` (store unchanged, mirroring `ExecProg.set_return_value`),
without touching `StepInstr`/`ExecProg`. The tests below show reachability now
gets past `SET_RETURN_VALUE` (and a following `DEAD`) to the assertion, and that
the previously-vacuous `ProgramSafe` now correctly fails. -/

/-- `SET_RETURN_VALUE 0; DEAD x; ASSERT false; END_FUNCTION`. The assertion at
    pc 2 is violable and sits after a `SET_RETURN_VALUE`. -/
def setReturnThenAssertProg : Program :=
  { name := "test"
    instructions := #[
      { type := .SET_RETURN_VALUE, locationNum := 0,
        code := Code.set_return_value (Expr.constant "0" .Integer) },
      { type := .DEAD, locationNum := 1,
        code := Code.dead (Expr.symbol "x" .Integer) },
      { type := .ASSERT, locationNum := 2,
        guard := Expr.constant "false" .Boolean,
        sourceLoc := { SourceLocation.nil with comment := "reachable after SET_RETURN_VALUE" } },
      { type := .END_FUNCTION, locationNum := 3 }
    ] }

-- Positive: the assertion's pc (2) IS reachable from pc 0 — reachability steps
-- past `SET_RETURN_VALUE` (via the new constructor) and then past `DEAD x` (via
-- an ordinary `StepInstr` step, which kills `x`).
example :
    Reachable noCall testEval (fun _ => none) setReturnThenAssertProg
      0 Store.empty 2 (Store.empty.kill "x") := by
  apply Reachable.step_set_return_value
  · rfl
  · apply Reachable.step (pc' := 2) (σ' := Store.empty.kill "x")
    · exact StepInstr.dead rfl rfl
    · exact Reachable.refl

-- Negative: the program is NOT safe. Before the fix this failed vacuously
-- because pc 2 was unreachable; now the violable assertion is actually reached.
example : ¬ ProgramSafe noCall testEval (fun _ => none) setReturnThenAssertProg
    Store.empty := by
  intro hsafe
  apply hsafe 2 (Store.empty.kill "x")
  · apply Reachable.step_set_return_value
    · rfl
    · apply Reachable.step (pc' := 2) (σ' := Store.empty.kill "x")
      · exact StepInstr.dead rfl rfl
      · exact Reachable.refl
  · exact ⟨rfl, rfl⟩

/-! ## Regression: nested `old()` in two-state evaluation

Previously the two-state evaluators only handled `old(...)` at the TOP LEVEL of
an expression. When `old(...)` appeared NESTED (e.g. `old(x) + 1`, common in
CBMC postconditions such as `result == old(x) + 1`), the top-level operator
(here `+`/`==`) dispatched to the single-state `concreteEval`, which has no
`Old` case and therefore returned `none`, failing the whole evaluation. The
two-state evaluation now recurses through itself carrying both stores, so
`old()` is handled at any nesting depth. -/

/-- `old(x)` with an integer operand. -/
private def oldX : Expr :=
  { id := .unary .Old, type := .Integer, operands := [Expr.symbol "x" .Integer] }

/-- `old(x) + 1` — `old` nested under `+`. -/
private def oldXPlus1 : Expr := Expr.add [oldX, Expr.constant "1" .Integer]

/-- `result == old(x) + 1` — `old` nested under `==`. -/
private def resultEqOldXPlus1 : Expr :=
  Expr.eq (Expr.symbol "result" .Integer) oldXPlus1

/-- `old(old(x))` — `old` nested inside `old`. -/
private def oldOldX : Expr :=
  { id := .unary .Old, type := .Integer, operands := [oldX] }

/-- Pre-state: `x = 10`. -/
private def preStore : Store := Store.empty.update "x" (.int 10)

/-- Current state: `x = 99`, `result = 11`. -/
private def curStore : Store :=
  (Store.empty.update "x" (.int 99)).update "result" (.int 11)

-- Demonstrates the bug: the single-state evaluator has no `Old` case, so a
-- nested `old(...)` makes it return `none`. (This is exactly why delegating a
-- non-`old` top-level node to the single-state evaluator was wrong.)
/-- info: true -/
#guard_msgs in
#eval concreteEval curStore oldXPlus1 == none

-- Fixed: `old(x)` reads `x` from the pre-state (10) and `+ 1` gives 11 — the
-- rest (there is none here) would read the current state. No longer `none`.
/-- info: true -/
#guard_msgs in
#eval concreteEval₂ preStore curStore oldXPlus1 == some (.int 11)

-- Nested `old` under a binary operator: `result` (11, current) equals
-- `old(x) + 1` (10 from pre-state, + 1 = 11).
/-- info: true -/
#guard_msgs in
#eval concreteEval₂ preStore curStore resultEqOldXPlus1 == some (.bool true)

-- `old(old(x))` stays in the pre-state: reads `x` from the pre-state (10).
/-- info: true -/
#guard_msgs in
#eval concreteEval₂ preStore curStore oldOldX == some (.int 10)

-- The generic `ExprEval.withOld` lift also handles nested `old()` now.
/-- info: true -/
#guard_msgs in
#eval ExprEval.withOld concreteEval preStore curStore oldXPlus1 == some (.int 11)

/-- info: true -/
#guard_msgs in
#eval ExprEval.withOld concreteEval preStore curStore resultEqOldXPlus1
        == some (.bool true)

-- Doubly-nested `old(old(x))` via the generic `ExprEval.withOld` lift as well:
-- `rewriteOld` treats the outer `old` as the maximal old-subterm and strips the
-- inner one, so `x` is read from the pre-state (10). This exercises nesting in
-- the `rewriteOld`/`stripOld` implementation, independent of `concreteEval₂`.
/-- info: true -/
#guard_msgs in
#eval ExprEval.withOld concreteEval preStore curStore oldOldX == some (.int 10)


/-! ## Regression: `with` (array update) is out-of-bounds checked

`List.set` is a silent no-op on an out-of-range index, so the `.ternary .«with»`
case previously returned `some (.array elems)` (the array unchanged) for an
out-of-bounds write — asymmetric with the `.binary .Index` case, which returns
`none` for the same OOB indices. That would mask violated write bounds once
correspondence-proof / symbolic-execution consumers land. The evaluator now
rejects an OOB `with` (index `< 0` or `≥ length`) with `none`, mirroring
`Index`. -/

private def boundsArrStore : Store :=
  Store.empty.update "a" (.array [.int 10, .int 20, .int 30])

private def boundsArr : Expr := Expr.symbol "a" .Integer
private def boundsIntC (n : Int) : Expr := Expr.constant (toString n) .Integer
private def boundsWith (i v : Int) : Expr :=
  { id := .ternary .«with», type := .Integer, operands := [boundsArr, boundsIntC i, boundsIntC v] }
private def boundsIndex (i : Int) : Expr :=
  { id := .binary .Index, type := .Integer, operands := [boundsArr, boundsIntC i] }

-- Sibling `Index` at an out-of-bounds index returns `none` (the behavior `with`
-- must mirror).
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsIndex 3) == none

-- An in-bounds `Index` returns the concrete element at that position (the
-- success path; the tests above/below only cover the `none` paths).
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsIndex 1) == some (.int 20)

-- A negative `Index` (not just negative `with`) is rejected with `none`.
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsIndex (-1)) == none

-- A negative `with` index is rejected.
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsWith (-1) 99) == none

-- An out-of-bounds `with` index is now rejected too (previously it silently
-- returned the array unchanged because `List.set` is a no-op there).
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsWith 3 99) == none

-- An in-bounds `with` still updates the element.
/-- info: true -/
#guard_msgs in
#eval concreteEval boundsArrStore (boundsWith 1 99)
        == some (.array [.int 10, .int 99, .int 30])


/-! ### Empty-array boundary: `Index` and `with` agree on `none`

The empty array is the degenerate boundary where the `i.toNat ≥ elems.length`
guard fires with both sides `0`. Both `Index` and `with` at index 0 on an empty
array must return `none`, confirming the two operations agree on this case (the
point of the OOB `with` fix). -/

private def emptyArrStore : Store :=
  Store.empty.update "a" (.array [])

/-- info: true -/
#guard_msgs in
#eval concreteEval emptyArrStore (boundsIndex 0) == none

/-- info: true -/
#guard_msgs in
#eval concreteEval emptyArrStore (boundsWith 0 42) == none


/-! ### Regression: division/modulo by zero returns `none`

Lean's `Int.div`/`Int.mod` are total (`_ / 0 = 0`), so `Div`/`Mod` used to
silently evaluate a zero divisor to `0`, masking what CBMC treats as undefined
behavior. The evaluator now returns `none` for a zero divisor; non-zero
divisors evaluate as before. -/

private def divModStore : Store := Store.empty
private def divE (a b : Int) : Expr :=
  { id := .binary .Div, type := .Integer, operands := [boundsIntC a, boundsIntC b] }
private def modE (a b : Int) : Expr :=
  { id := .binary .Mod, type := .Integer, operands := [boundsIntC a, boundsIntC b] }

/-- info: true -/
#guard_msgs in
#eval concreteEval divModStore (divE 6 0) == none

/-- info: true -/
#guard_msgs in
#eval concreteEval divModStore (modE 6 0) == none

-- Non-zero divisors are unaffected.
/-- info: true -/
#guard_msgs in
#eval concreteEval divModStore (divE 7 2) == some (.int 3)

/-- info: true -/
#guard_msgs in
#eval concreteEval divModStore (modE 7 2) == some (.int 1)


/-! ### Boundary: empty multiary `Plus`/`Mult` are the additive/multiplicative identity

An empty operand list is the degenerate boundary of the multiary `Plus`/`Mult`
cases (`[] => some (.int 0)` / `some (.int 1)`). These identity branches are
exercised here directly. -/

private def emptyPlus : Expr :=
  { id := .multiary .Plus, type := .Integer, operands := [] }
private def emptyMult : Expr :=
  { id := .multiary .Mult, type := .Integer, operands := [] }

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty emptyPlus == some (.int 0)

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty emptyMult == some (.int 1)


/-! ### Bitvector arithmetic/comparison/negation is rejected (pending width normalization)

Applying the integer operation to a bitvector's stored `Int` without wrapping
modulo `2^w` would be unsound BV arithmetic, so BV operands to arithmetic,
comparison, and negation now return `none` rather than a subtly-wrong result.
Bitvector `constant`s and `Typecast`s remain handled (see the Typecast tests
below); only the arithmetic/comparison/negation paths reject BV. -/

private def bvStore : Store :=
  (Store.empty.update "p" (.bv 32 3)).update "q" (.bv 32 4)
private def bvP : Expr := Expr.symbol "p" .Integer
private def bvQ : Expr := Expr.symbol "q" .Integer
private def bvPlus : Expr :=
  { id := .multiary .Plus, type := .Integer, operands := [bvP, bvQ] }
private def bvMult : Expr :=
  { id := .multiary .Mult, type := .Integer, operands := [bvP, bvQ] }
private def bvMinus : Expr :=
  { id := .binary .Minus, type := .Integer, operands := [bvP, bvQ] }
private def bvDiv : Expr :=
  { id := .binary .Div, type := .Integer, operands := [bvP, bvQ] }
private def bvLt : Expr :=
  { id := .binary .Lt, type := .Boolean, operands := [bvP, bvQ] }
private def bvNeg : Expr :=
  { id := .unary .UnaryMinus, type := .Integer, operands := [bvP] }

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvPlus == none

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvMult == none

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvMinus == none

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvDiv == none

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvLt == none

/-- info: true -/
#guard_msgs in
#eval concreteEval bvStore bvNeg == none


/-! ### Typecast coverage: the `.unary .Typecast` path and `typeCast` arms

`typeCast` (via the `Typecast` unary operator) is exercised by none of the other
tests, yet the Core→GOTO translation emits typecasts that feed the arithmetic
and comparison operators. Pin the main conversions. -/

private def castBoolToInt : Expr :=
  { id := .unary .Typecast, type := .Integer, operands := [Expr.constant "true" .Boolean] }
private def castIntToBool : Expr :=
  { id := .unary .Typecast, type := .Boolean, operands := [Expr.constant "5" .Integer] }
private def castIntToBV : Expr :=
  { id := .unary .Typecast, type := Ty.SignedBV 32, operands := [Expr.constant "7" .Integer] }
private def castBVToBV : Expr :=
  { id := .unary .Typecast, type := Ty.SignedBV 32, operands := [Expr.constant "3" (Ty.SignedBV 8)] }

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty castBoolToInt == some (.int 1)

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty castIntToBool == some (.bool true)

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty castIntToBV == some (.bv 32 7)

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty castBVToBV == some (.bv 32 3)


/-! ### GOTO taken branch: `goto_taken` + `findLocIdx`

A GOTO with a true guard resolves its `target` locationNum to an instruction
index via `findLocIdx` and jumps there, skipping the fall-through instruction.
This exercises `StepInstr.goto_taken` and `findLocIdx`, untested otherwise. -/

def gotoTakenProg : Program :=
  { name := "test"
    instructions := #[
      { type := .GOTO, locationNum := 0,
        guard := Expr.constant "true" .Boolean, target := some 2 },
      { type := .SKIP, locationNum := 1 },        -- skipped by the taken branch
      { type := .END_FUNCTION, locationNum := 2 }
    ] }

-- The guard is true, so execution jumps from pc 0 straight to the END_FUNCTION
-- at index 2 (locationNum 2, resolved by findLocIdx), never running the SKIP.
example : ExecProg noCall testEval (fun _ => none) gotoTakenProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 2)
  · exact StepInstr.goto_taken rfl rfl rfl rfl
  · exact ExecProg.end_function rfl


/-! ### `ProgramSafe ↔ ¬ CanFail` alignment with `Specification.lean`

`assertFailProg` reaches (at pc 0) a failing assertion, so it `CanFail`. Via
`programSafe_iff_not_canFail`, that witness is exactly what refutes
`ProgramSafe` — mirroring `Specification.lean`'s `CanFail`/overapproximation
shape at the GOTO-IL layer. -/

-- `assertFailProg` can fail: pc 0 is reachable (reflexively) and its ASSERT
-- guard evaluates to `false`.
example : CanFail noCall testEval (fun _ => none) assertFailProg Store.empty :=
  ⟨0, Store.empty, Reachable.refl, rfl, rfl⟩

-- ...and lack of safety follows from that witness through the alignment lemma.
example : ¬ ProgramSafe noCall testEval (fun _ => none) assertFailProg Store.empty :=
  fun hsafe =>
    (programSafe_iff_not_canFail.mp hsafe) ⟨0, Store.empty, Reachable.refl, rfl, rfl⟩


/-! ## Regression: ASSUME pass advances; false guard blocks (AutoSDE)

`assume_pass` is the only `StepInstr` rule for ASSUME (guard true → advance).
A false guard admits NO `StepInstr` derivation — the path is infeasible — and
`progress_assume` returns the `AssumeBlocks` disjunct instead of a step. -/

def assumePassProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSUME, locationNum := 0, guard := Expr.constant "true" .Boolean },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- ASSUME true advances (assume_pass) and the program runs to completion.
example : ExecProg noCall testEval (fun _ => none) assumePassProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.assume_pass rfl rfl
  · exact ExecProg.end_function rfl

def assumeFalseProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSUME, locationNum := 0, guard := Expr.constant "false" .Boolean },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- ASSUME false blocks: the `AssumeBlocks` predicate holds at pc 0.
example : AssumeBlocks testEval assumeFalseProg 0 Store.empty := ⟨rfl, rfl⟩

-- ...and there is NO `StepInstr` derivation from a false ASSUME (infeasible path):
-- the only ASSUME rule (`assume_pass`) needs a true guard, and every other rule
-- needs a different `instrType`.
example : ¬ ∃ pc' σ',
    StepInstr noCall testEval (fun _ => none) assumeFalseProg 0 Store.empty pc' σ' := by
  rintro ⟨pc', σ', hstep⟩
  cases hstep <;> simp_all [instrType, instrGuard, assumeFalseProg, testEval, Expr.constant]

-- `progress_assume` returns the blocking (`AssumeBlocks`) disjunct, not a step.
example :
    progress_assume (callResult := noCall) (eval := testEval) (fenv := fun _ => none)
      (prog := assumeFalseProg) (pc := 0) (σ := Store.empty) rfl ⟨false, rfl⟩
    = Or.inr ⟨rfl, rfl⟩ := rfl


/-! ## Regression: bitvector values are normalized modulo 2^w (sound structural ==)

`parseConstant`/`typeCast` build `Value.bv` via `mkBv`, which reduces the stored
integer to `[0, 2^w)`. So an out-of-range literal and its in-range representative
are the SAME value and structural `Equal` is sound: `256` and `0` are equal as
8-bit values (previously `.bv 8 256` ≠ `.bv 8 0`). -/

private def castTo8 (n : Int) : Expr :=
  { id := .unary .Typecast, type := Ty.UnsignedBV 8,
    operands := [Expr.constant (toString n) .Integer] }
private def bvEq (a b : Expr) : Expr :=
  { id := .binary .Equal, type := .Boolean, operands := [a, b] }

-- 256 typecast to an 8-bit BV normalizes to the bit pattern 0.
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty (castTo8 256) == some (.bv 8 0)

-- ...and it compares structurally equal to the 8-bit representative of 0.
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty (bvEq (castTo8 256) (castTo8 0)) == some (.bool true)

-- A NEGATIVE integer typecast to an 8-bit BV normalizes to its non-negative
-- representative `255` (Euclidean `emod`), not the truncated `-1` — so it is
-- structurally equal to the 8-bit representative of 255, keeping `Equal` sound.
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty (castTo8 (-1)) == some (.bv 8 255)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty (bvEq (castTo8 (-1)) (castTo8 255)) == some (.bool true)


/-! ## Regression: concrete-output coverage for the integer/logical operators (AutoSDE)

`concreteEval` arms for integer `Minus`, the integer comparisons
(`Lt`/`Le`/`Gt`/`Ge` on the `.int` path — the BV tests only pin their
rejection), `Not`, multiary `And`/`Or`, `Implies`, and `ite` had no concrete
positive-output test. Pin one concrete result per operator family. -/

private def iC (n : Int) : Expr := Expr.constant (toString n) .Integer
private def bC (b : Bool) : Expr := Expr.constant (if b then "true" else "false") .Boolean
private def minusE : Expr := { id := .binary .Minus, type := .Integer, operands := [iC 5, iC 3] }
private def ltE : Expr := { id := .binary .Lt, type := .Boolean, operands := [iC 3, iC 5] }
private def leE : Expr := { id := .binary .Le, type := .Boolean, operands := [iC 5, iC 5] }
private def gtE : Expr := { id := .binary .Gt, type := .Boolean, operands := [iC 5, iC 3] }
private def geE : Expr := { id := .binary .Ge, type := .Boolean, operands := [iC 3, iC 5] }
private def notTrueE : Expr := { id := .unary .Not, type := .Boolean, operands := [bC true] }
private def andE : Expr := { id := .multiary .And, type := .Boolean, operands := [bC true, bC false] }
private def orE : Expr := { id := .multiary .Or, type := .Boolean, operands := [bC false, bC true] }
private def impliesE : Expr := { id := .binary .Implies, type := .Boolean, operands := [bC true, bC false] }
private def iteTrueE : Expr := { id := .ternary .ite, type := .Integer, operands := [bC true, iC 1, iC 2] }
private def iteFalseE : Expr := { id := .ternary .ite, type := .Integer, operands := [bC false, iC 1, iC 2] }

/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty minusE == some (.int 2)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty ltE == some (.bool true)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty leE == some (.bool true)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty gtE == some (.bool true)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty geE == some (.bool false)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty notTrueE == some (.bool false)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty andE == some (.bool false)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty orE == some (.bool true)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty impliesE == some (.bool false)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty iteTrueE == some (.int 1)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty iteFalseE == some (.int 2)

private def neqTrueE : Expr := { id := .binary .NotEqual, type := .Boolean, operands := [iC 1, iC 2] }
private def neqFalseE : Expr := { id := .binary .NotEqual, type := .Boolean, operands := [iC 3, iC 3] }
-- `NotEqual` is a distinct `evalCore` arm from `Equal` (tested via `bvEq`); pin
-- both truth values so an accidental `==`/`!=` swap would be caught.
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty neqTrueE == some (.bool true)
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty neqFalseE == some (.bool false)

private def intNeg : Expr := { id := .unary .UnaryMinus, type := .Integer, operands := [iC 5] }
private def multInts : Expr := { id := .multiary .Mult, type := .Integer, operands := [iC 2, iC 3, iC 7] }
-- `.unary .UnaryMinus` on an `.int` (the success arm; `bvNeg` only covers the BV rejection).
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty intNeg == some (.int (-5))
-- Non-empty integer `.multiary .Mult` (`emptyMult` covers `[] → 1`; `bvMult` the BV rejection).
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty multInts == some (.int 42)


/-! ## Regression: `ExecProg`-level ASSIGN and FUNCTION_CALL pin the post-store (AutoSDE)

The existing `ExecProg` examples exercise SKIP/ASSERT/DEAD/GOTO/ASSUME/
SET_RETURN_VALUE but never `ASSIGN` (the store-updating rule) or `FUNCTION_CALL`.
These pin the resulting store. -/

def assignProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSIGN, locationNum := 0,
        code := Code.assign (Expr.symbol "x" .Integer) (Expr.symbol "y" .Integer) },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- Starting from `y ↦ 42`, `ASSIGN x := y` evaluates the rhs and updates the
-- store so `x ↦ .int 42`, then END_FUNCTION halts.
example :
    ExecProg noCall testEval (fun _ => none) assignProg 0
      (Store.empty.update "y" (.int 42))
      ((Store.empty.update "y" (.int 42)).update "x" (.int 42)) none := by
  apply ExecProg.step (pc' := 1)
    (σ' := (Store.empty.update "y" (.int 42)).update "x" (.int 42))
  · exact StepInstr.assign (name := "x") (rhs := Expr.symbol "y" .Integer) (v := .int 42)
      rfl rfl rfl (by simp [testEval, Store.update, Expr.symbol])
  · exact ExecProg.end_function rfl

/-- A call relation that runs `callee` to a fixed return value `7`, store unchanged. -/
def fixedCall : CallResultRel := fun _ _ name σ σ' rv =>
  name = "callee" ∧ σ' = σ ∧ rv = some (.int 7)

/-- A `FUNCTION_CALL` whose code names lhs `r` and callee `callee`. Only the code
    operands are read by the semantics (`getCallLhs`/`getCallCallee`), so the
    `Code.id` is immaterial here. -/
def callProg : Program :=
  { name := "test"
    instructions := #[
      { type := .FUNCTION_CALL, locationNum := 0,
        code := { id := default,
                  operands := [Expr.symbol "r" .Integer, Expr.symbol "callee" .Integer,
                               Expr.symbol "r" .Integer] } },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- The call binds the callee's return value (7) to the lhs `r`: `r ↦ .int 7`.
example : ExecProg fixedCall testEval (fun _ => none) callProg 0
    Store.empty (Store.empty.update "r" (.int 7)) none := by
  apply ExecProg.step (pc' := 1) (σ' := Store.empty.update "r" (.int 7))
  · exact StepInstr.function_call rfl rfl ⟨rfl, rfl, rfl⟩ rfl
  · exact ExecProg.end_function rfl


/-! ## Regression: uncovered `parseConstant`/`evalCore` arms and `ExecProg` return propagation (AutoSDE)

`parseConstant`'s `.string`/`.real` arms, `evalCore`'s `.nullary .nil` arm, and
the `ExecProg.set_return_value` return-value propagation (`retVal <|> some v`)
each had no test — every prior `ExecProg` example produced a `none` return. -/

-- `parseConstant` string arm: the literal is taken verbatim as a string value.
/-- info: true -/
#guard_msgs in
#eval parseConstant "hello" .String == some (.string "hello")

-- `parseConstant` real arm: an integer literal becomes the rational `n/1`.
/-- info: true -/
#guard_msgs in
#eval parseConstant "3" .Real == some (.rational 3 1)

-- `evalCore`'s `.nullary .nil` arm returns the `undefined` sentinel.
private def nilE : Expr := { id := .nullary .nil, type := .Integer, operands := [] }
/-- info: true -/
#guard_msgs in
#eval concreteEval Store.empty nilE == some .undefined

-- `ExecProg.set_return_value` propagates the evaluated return value: a
-- SET_RETURN_VALUE(true) followed by END_FUNCTION yields `some (.bool true)` —
-- the only `ExecProg` path producing a non-`none` return.
def setReturnProg : Program :=
  { name := "test"
    instructions := #[
      { type := .SET_RETURN_VALUE, locationNum := 0,
        code := Code.set_return_value (Expr.constant "true" .Boolean) },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example : ExecProg noCall testEval (fun _ => none) setReturnProg 0
    Store.empty Store.empty (some (.bool true)) := by
  exact ExecProg.set_return_value (retVal := none) (v := .bool true) rfl rfl
    (by simp [testEval, Expr.constant]) (ExecProg.end_function rfl)

