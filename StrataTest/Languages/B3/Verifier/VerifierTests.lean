/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion
import Strata.DL.SMT.Solver

/-!
# B3 Verifier Integration Tests

Tests for B3 verification with SMT solvers (Z3/CVC5).
These tests run the actual solver and test check, assert, reach statements with automatic diagnosis.

## Implementation Status

**Expressions:**
- ✅ Literals (int, bool, string)
- ✅ Binary operators (==, !=, <, <=, >, >=, +, -, *, div, mod, &&, ||, ==>, <==, <==>)
- ✅ Unary operators (!, -)
- ✅ If-then-else
- ✅ Function calls
- ✅ Quantifiers (forall, exists) with patterns
- ✅ Labeled expressions (labels stripped)
- ❌ Let expressions (needs proper substitution)

**Declarations:**
- ✅ Function declarations
- ✅ Function bodies → quantified axioms
- ✅ Axioms
- ❌ Explains clauses (parsed but ignored)
- ❌ Type declarations
- ❌ Tagger declarations
- ❌ Injective parameters → inverse functions
- ❌ Tagged functions → tag constants
- ❌ When clauses (parsed but not fully tested)

**Statements:**
- ✅ Check (verify property)
- ✅ Assert (verify and assume)
- ✅ Assume (add to solver)
- ✅ Reach (reachability)
- ✅ Block statements
- ❌ Probe statements
- ❌ Variable declarations (var, val)
- ❌ Assignments
- ❌ Reinit
- ❌ If statements
- ❌ If-case statements
- ❌ Choose statements
- ❌ Loop statements with invariants
- ❌ Labeled statements
- ❌ Exit/Return statements
- ❌ Forall statements (aForall)

**Procedures:**
- ✅ Parameter-free procedures
- ❌ Procedures with parameters (in, out, inout)

**Error Handling:**
- ✅ Error accumulation (conversion errors don't short-circuit)
- ✅ Pattern validation with error reporting
- ✅ Recursive diagnosis of failing conjunctions
- ✅ Context-aware diagnosis (assumes earlier conjuncts when diagnosing later ones)

-/

namespace B3.Verifier.Tests

open Strata
open Strata.B3.Verifier
open Strata.SMT

---------------------------------------------------------------------
-- Test Helpers
---------------------------------------------------------------------

-- Diagnostic message constants for consistency
private def MSG_COULD_NOT_PROVE := "could not prove"
private def MSG_IMPOSSIBLE := "it is impossible that"
private def MSG_UNDER_ASSUMPTIONS := "under the assumptions"

def formatSourceLocation (baseOffset : String.Pos.Raw) (sr : SourceRange) : String :=
  let relativePos := sr.start.byteIdx - baseOffset.byteIdx
  s!"(0,{relativePos})"

def formatStatementError (prog : Program) (stmt : B3AST.Statement SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := formatSourceLocation baseOffset stmt.metadata
  let formatted := formatStatement prog stmt B3.ToCSTContext.empty
  s!"{loc}: {formatted}"

def formatExpressionError (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := formatSourceLocation baseOffset (getExpressionMetadata expr)

  let formatted := formatExpression prog expr B3.ToCSTContext.empty

  s!"{loc}: {formatted}"

def formatExpressionLocation (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  formatSourceLocation baseOffset (getExpressionMetadata expr)

def formatExpressionOnly (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let (cstExpr, _) := B3.expressionToCST B3.ToCSTContext.empty expr
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trim

/-- Flatten conjunctions into a list of conjuncts for display -/
def flattenConjunction : B3AST.Expression SourceRange → List (B3AST.Expression SourceRange)
  | .binaryOp _ (.and _) lhs rhs => flattenConjunction lhs ++ flattenConjunction rhs
  | expr => [expr]
  termination_by e => SizeOf.sizeOf e

def testVerification (prog : Program) : IO Unit := do
  let result : Except String (B3AST.Program SourceRange) := programToB3AST prog
  let ast ← match result with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")
  -- Create a fresh solver for each test to avoid state issues
  let solver ← createInteractiveSolver "cvc5"
  let reports ← programToSMT ast solver
  -- Don't call exit - let the solver process terminate naturally
  for report in reports do
    for (result, diagnosis) in report.results do
      match result.context.decl with
      | .procedure _ name _ _ _ =>
          let marker := if result.result.isError then "✗" else "✓"
          let description := match result.result with
            | .error .counterexample => "counterexample found"
            | .error .unknown => "unknown"
            | .error .refuted => "refuted"
            | .success .verified => "verified"
            | .success .reachable => "reachable"
            | .success .reachabilityUnknown => "reachability unknown"

          IO.println s!"{name.val}: {marker} {description}"
          if result.result.isError then
            let baseOffset := match prog.commands.toList with
              | [op] => op.ann.start
              | _ => { byteIdx := 0 }

            let stmt := result.context.stmt
            IO.println s!"  {formatStatementError prog stmt}"

                -- Display diagnosis with VC for each failure, or top-level VC if no diagnosis
                match diagnosis with
                | some diag =>
                    if !diag.diagnosedFailures.isEmpty then
                      -- Show diagnosis with assumptions for each failure
                      for failure in diag.diagnosedFailures do
                        let exprLoc := formatExpressionLocation prog failure.expression
                        let exprFormatted := formatExpressionOnly prog failure.expression
                        let diagnosisPrefix := match failure.report.result with
                          | .error .refuted => MSG_IMPOSSIBLE
                          | .error .counterexample | .error .unknown => MSG_COULD_NOT_PROVE
                          | .success _ => MSG_COULD_NOT_PROVE  -- Shouldn't happen

                        -- Get statement location for comparison
                        let stmtLoc := match stmt with
                          | .check m _ | .assert m _ | .reach m _ => formatSourceLocation baseOffset m
                          | _ => ""

                        -- Only show location if different from statement location
                        if exprLoc == stmtLoc then
                          IO.println s!"  └─ {diagnosisPrefix} {exprFormatted}"
                        else
                          IO.println s!"  └─ {exprLoc}: {diagnosisPrefix} {exprFormatted}"

                        -- Show assumptions for this failure (from report context)
                        if !failure.report.context.pathCondition.isEmpty then
                          IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
                          for expr in failure.report.context.pathCondition.reverse do
                            -- Flatten conjunctions to show each on separate line
                            for conjunct in flattenConjunction expr do
                              let formatted := formatExpressionOnly prog conjunct
                              IO.println s!"       {formatted}"
                    else
                      -- No specific diagnosis - use same format with └─
                      if !result.context.pathCondition.isEmpty then
                        match stmt with
                        | .check m expr | .assert m expr =>
                            let exprLoc := formatSourceLocation baseOffset m
                            let formatted := formatExpressionOnly prog expr
                            IO.println s!"  └─ {exprLoc}: {MSG_COULD_NOT_PROVE} {formatted}"
                            IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
                            for expr in result.context.pathCondition.reverse do
                              -- Flatten conjunctions to show each on separate line
                              for conjunct in flattenConjunction expr do
                                let formatted := formatExpressionOnly prog conjunct
                                IO.println s!"       {formatted}"
                        | .reach m expr =>
                            let exprLoc := formatSourceLocation baseOffset m
                            let formatted := formatExpressionOnly prog expr
                            IO.println s!"  └─ {exprLoc}: {MSG_IMPOSSIBLE} {formatted}"
                            IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
                            for expr in result.context.pathCondition.reverse do
                              -- Flatten conjunctions to show each on separate line
                              for conjunct in flattenConjunction expr do
                                let formatted := formatExpressionOnly prog conjunct
                                IO.println s!"       {formatted}"
                        | _ => pure ()
                | none =>
                    -- No diagnosis - use same format with └─
                    if !result.context.pathCondition.isEmpty then
                      match stmt with
                      | .check m expr | .assert m expr =>
                          let exprLoc := formatSourceLocation baseOffset m
                          let formatted := formatExpressionOnly prog expr
                          IO.println s!"  └─ {exprLoc}: {MSG_COULD_NOT_PROVE} {formatted}"
                          IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
                          for expr in result.context.pathCondition.reverse do
                            -- Flatten conjunctions to show each on separate line
                            for conjunct in flattenConjunction expr do
                              let formatted := formatExpressionOnly prog conjunct
                              IO.println s!"       {formatted}"
                      | .reach m expr =>
                          let exprLoc := formatSourceLocation baseOffset m
                          let formatted := formatExpressionOnly prog expr
                          IO.println s!"  └─ {exprLoc}: {MSG_IMPOSSIBLE} {formatted}"
                          IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
                          for expr in result.context.pathCondition.reverse do
                            -- Flatten conjunctions to show each on separate line
                            for conjunct in flattenConjunction expr do
                              let formatted := formatExpressionOnly prog conjunct
                              IO.println s!"       {formatted}"
                      | _ => pure ()
      | _ => pure ()

---------------------------------------------------------------------
-- Example from Verifier.lean Documentation
---------------------------------------------------------------------

/--
info: Statement: check 8 == 8 && f(5) == 7
✗ Unknown
  Path condition:
    forall x : int pattern f(x) f(x) == x + 1
  Found 1 diagnosed failures
Failing expression: f(5) == 7
✗ Refuted (proved false/unreachable)
  Path condition:
    8 == 8
    forall x : int pattern f(x) f(x) == x + 1
-/
#guard_msgs in
#eval exampleVerification

---------------------------------------------------------------------
-- Check Statement Tests
---------------------------------------------------------------------

/--
info: test_checks_are_not_learned: ✗ unknown
  (0,113): check f(5) > 1
  └─ (0,113): could not prove f(5) > 1
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
test_checks_are_not_learned: ✗ unknown
  (0,130): check f(5) > 1
  └─ (0,130): could not prove f(5) > 1
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_checks_are_not_learned() {
  check f(5) > 1
  check f(5) > 1
}
#end

/--
info: test: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

/--
info: test_fail: ✗ counterexample found
  (0,52): check 5 == 5 && f(5) == 10
  └─ (0,68): could not prove f(5) == 10
     under the assumptions
       5 == 5
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end


/--
info: test_all_expressions: ✗ unknown
  (0,127): check (false || true) && (if true true else false) && f(5) && notalwaystrue(1, 2) && 5 == 5 && !(3 == 4) && 2 < 3 && 2 <= 2 && 4 > 3 && 4 >= 4 && 1 + 2 == 4 && 5 - 2 == 3 && 3 * 4 == 12 && 10 div 2 == 5 && 7 mod 3 == 1 && -(5) == 0 - 5 && notalwaystrue(3, 4) && (true ==> true) && (forall y : int pattern f(y) f(y) || !f(y)) && (forall y : int y > 0 || y <= 0)
  └─ (0,213): could not prove notalwaystrue(1, 2)
     under the assumptions
       forall x : int pattern f(x) f(x) == (x + 1 == 6)
       false || true
       if true true else false
       f(5)
  └─ (0,353): it is impossible that 1 + 2 == 4
     under the assumptions
       forall x : int pattern f(x) f(x) == (x + 1 == 6)
       false || true
       if true true else false
       f(5)
       notalwaystrue(1, 2)
       5 == 5
       !(3 == 4)
       2 < 3
       2 <= 2
       4 > 3
       4 >= 4
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : bool { x + 1 == 6 }
function notalwaystrue(a : int, b : int) : bool
procedure test_all_expressions() {
  check (false || true) &&
        (if true true else false) &&
        f(5) &&
        notalwaystrue(1, 2) &&
        5 == 5 &&
        !(3 == 4) &&
        2 < 3 &&
        2 <= 2 &&
        4 > 3 &&
        4 >= 4 &&
        1 + 2 == 4 && // The second error that should be spot
        5 - 2 == 3 &&
        3 * 4 == 12 &&
        10 div 2 == 5 &&
        7 mod 3 == 1 &&
        -5 == 0 - 5 &&
        notalwaystrue(3, 4) && // Not an error because we assumed false
        (true ==> true) &&
        (forall y : int pattern f(y) f(y) || !f(y)) &&
        (forall y : int y > 0 || y <= 0)
}
#end

---------------------------------------------------------------------
-- Assert Statement Tests
---------------------------------------------------------------------

-- Assertions are assumed so further checks pass
/--
info: test_assert_helps: ✗ unknown
  (0,103): assert f(5) > 1
  └─ (0,103): could not prove f(5) > 1
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
test_assert_helps: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_assert_helps() {
  assert f(5) > 1
  check f(5) > 1
}
#end

/--
info: test_assert_with_trace: ✗ unknown
  (0,138): assert f(5) > 10
  └─ (0,138): could not prove f(5) > 10
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
       f(1) > 0
       f(4) > 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_assert_with_trace() {
  assume f(1) > 0 && f(4) > 0
  assert f(5) > 10
}
#end

---------------------------------------------------------------------
-- Reach Statement Tests
---------------------------------------------------------------------

/--
info: test_reach_bad: ✗ refuted
  (0,100): reach f(5) < 0
  └─ (0,100): it is impossible that f(5) < 0
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_bad() {
  reach f(5) < 0
}
#end

/--
info: test_reach_good: ✓ reachability unknown
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_good() {
  reach f(5) > 5
}
#end

/--
info: test_reach_with_trace: ✗ refuted
  (0,137): reach f(5) < 0
  └─ (0,137): it is impossible that f(5) < 0
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
       f(1) > 0
       f(4) > 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_with_trace() {
  assume f(1) > 0 && f(4) > 0
  reach f(5) < 0
}
#end

---------------------------------------------------------------------
-- Automatic Diagnosis Tests
---------------------------------------------------------------------

/--
info: test_reach_diagnosis: ✗ refuted
  (0,106): reach f(5) > 5 && f(5) < 0
  └─ (0,124): it is impossible that f(5) < 0
     under the assumptions
       forall x : int pattern f(x) f(x) > 0
       f(5) > 5
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_diagnosis() {
  reach f(5) > 5 && f(5) < 0
}
#end



/--
info: test_all_expressions: ✗ refuted
  (0,127): reach (false || true) && (if true true else false) && f(5) && notalwaystrue(1, 2) && 5 == 5 && !(3 == 4) && 2 < 3 && 2 <= 2 && 4 > 3 && 4 >= 4 && 1 + 2 == 4 && 5 - 2 == 3 && 3 * 4 == 12 && 10 div 2 == 5 && 7 mod 3 == 1 && -(5) == 0 - 5 && notalwaystrue(3, 4) && (true ==> true) && (forall y : int pattern f(y) f(y) || !f(y)) && (forall y : int y > 0 || y <= 0)
  └─ (0,353): it is impossible that 1 + 2 == 4
     under the assumptions
       forall x : int pattern f(x) f(x) == (x + 1 == 6)
       false || true
       if true true else false
       f(5)
       notalwaystrue(1, 2)
       5 == 5
       !(3 == 4)
       2 < 3
       2 <= 2
       4 > 3
       4 >= 4
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : bool { x + 1 == 6 }
function notalwaystrue(a : int, b : int) : bool
procedure test_all_expressions() {
  reach (false || true) &&
        (if true true else false) &&
        f(5) &&
        notalwaystrue(1, 2) &&
        5 == 5 &&
        !(3 == 4) &&
        2 < 3 &&
        2 <= 2 &&
        4 > 3 &&
        4 >= 4 &&
        1 + 2 == 4 && // First unreachable - diagnosis stops here
        5 - 2 == 3 &&
        3 * 4 == 12 &&
        10 div 2 == 5 &&
        7 mod 3 == 1 &&
        -5 == 0 - 5 &&
        notalwaystrue(3, 4) &&
        (true ==> true) &&
        (forall y : int pattern f(y) f(y) || !f(y)) &&
        (forall y : int y > 0 || y <= 0)
}
#end



/--
info: test_all_expressions: ✗ refuted
  (0,85): reach notalwaystrue(1, 2) && !notalwaystrue(1, 2) && 5 == 4
  └─ (0,122): it is impossible that !notalwaystrue(1, 2)
     under the assumptions
       notalwaystrue(1, 2)
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function notalwaystrue(a : int, b : int) : bool
procedure test_all_expressions() {
  reach notalwaystrue(1, 2) &&
        !notalwaystrue(1, 2) &&
        5 == 4
}
#end
end B3.Verifier.Tests
