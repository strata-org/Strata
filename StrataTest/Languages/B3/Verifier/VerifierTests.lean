/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.Format
import Strata.Languages.B3.FromCore
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
open B3.Verifier
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
  (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trimAscii.toString

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
  let solver ← Solver.spawn "cvc5" #["--quiet", "--lang", "smt", "--incremental", "--produce-models"]
  let reports ← B3.Verifier.programToSMT ast solver
  for report in reports do
    for (result, _) in report.results do
      let marker := match result.outcome with
        | .pass => "✓"
        | .fail => "✗"
        | .unknown => "✗"
        | .implementationError _ => "✗"
      
      let description := match result.outcome with
        | .pass => "verified"
        | .fail => "counterexample found"
        | .unknown => "unknown"
        | .implementationError msg => s!"error: {msg}"

      IO.println s!"{result.label}: {marker} {description}"
      if result.outcome != .pass then
        -- Show the statement (obligation expression converted to B3)
        match result.obligation with
        | some obl =>
          match B3.FromCore.exprFromCore obl.obligation with
          | .ok b3Stmt =>
            -- Use statement source range from metadata if available, else expression location
            let stmtLoc := match Imperative.getFileRange obl.metadata with
              | some fr => formatSourceLocation (match prog.commands.toList with
                  | [op] => op.ann.start | _ => { byteIdx := 0 }) fr.range
              | none => formatExpressionLocation prog b3Stmt
            let stmtFormatted := formatExpressionOnly prog b3Stmt
            let stmtKind := if obl.property == .cover then "reach" else "check"
            IO.println s!"  {stmtLoc}: {stmtKind} {stmtFormatted}"
          | .error _ => pure ()
        | none => pure ()
        -- Show diagnosis if available
        match result.diagnosis with
        | some diag =>
          for failure in diag.diagnosedFailures do
            let diagnosisPrefix := match failure.report.result with
              | .error .refuted => MSG_IMPOSSIBLE
              | .error .counterexample | .error .unknown => MSG_COULD_NOT_PROVE
              | .ok _ => MSG_COULD_NOT_PROVE
            match B3.FromCore.exprFromCore failure.expression with
            | .ok b3Expr =>
              let exprLoc := formatExpressionLocation prog b3Expr
              let exprFormatted := formatExpressionOnly prog b3Expr
              IO.println s!"  └─ {exprLoc}: {diagnosisPrefix} {exprFormatted}"
            | .error _ =>
              IO.println s!"  └─ {diagnosisPrefix} <expression>"
            -- Show assumptions
            if !failure.report.context.pathCondition.isEmpty then
              IO.println s!"     {MSG_UNDER_ASSUMPTIONS}"
              for assumption in failure.report.context.pathCondition.reverse do
                match B3.FromCore.exprFromCore assumption with
                | .ok b3Assumption =>
                  let formatted := formatExpressionOnly prog b3Assumption
                  IO.println s!"       {formatted}"
                | .error _ => IO.println s!"       <assumption>"
        | none => pure ()

---------------------------------------------------------------------
-- Example from Verifier.lean Documentation
---------------------------------------------------------------------

-- /--
-- info: Statement: check 8 == 8 && f(5) == 7
-- ✗ Unknown
--   Path condition:
--     forall x : int pattern f(x) f(x) == x + 1
--   Found 1 diagnosed failures
-- Failing expression: f(5) == 7
-- ✗ Refuted (proved false/unreachable)
--   Path condition:
--     8 == 8
--     forall x : int pattern f(x) f(x) == x + 1
-- -/
-- #guard_msgs in
-- #eval exampleVerification

---------------------------------------------------------------------
-- Check Statement Tests
---------------------------------------------------------------------

/--
info: test_checks_are_not_learned: ✗ unknown
  (0,113): check f(5) > 1
  └─ (0,119): could not prove f(5) > 1
     under the assumptions
       forall x0 : int f(x0) > 0
test_checks_are_not_learned: ✗ unknown
  (0,130): check f(5) > 1
  └─ (0,136): could not prove f(5) > 1
     under the assumptions
       forall x0 : int f(x0) > 0
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
  └─ (0,58): could not prove 5 == 5
  └─ (0,68): could not prove f(5) == 10
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end


/--
info: test_all_expressions: ✗ counterexample found
  (0,127): check (false || true) && (if true true else false) && f(5) && notalwaystrue(1, 2) && 5 == 5 && !(3 == 4) && 2 < 3 && 2 <= 2 && 4 > 3 && 4 >= 4 && 1 + 2 == 4 && 5 - 2 == 3 && 3 * 4 == 12 && 10 div 2 == 5 && 7 mod 3 == 1 && -5 == 0 - 5 && notalwaystrue(3, 4) && (true ==> true) && (forall x0 : int f(x0) || !f(x0)) && (forall x0 : int x0 > 0 || x0 <= 0)
  └─ (0,134): could not prove false || true
  └─ (0,161): could not prove if true true else false
  └─ (0,197): could not prove f(5)
  └─ (0,213): could not prove notalwaystrue(1, 2)
  └─ (0,244): could not prove 5 == 5
  └─ (0,262): could not prove !(3 == 4)
  └─ (0,283): could not prove 2 < 3
  └─ (0,300): could not prove 2 <= 2
  └─ (0,318): could not prove 4 > 3
  └─ (0,335): could not prove 4 >= 4
  └─ (0,353): it is impossible that 1 + 2 == 4
  └─ (0,415): it is impossible that 5 - 2 == 3
  └─ (0,437): it is impossible that 3 * 4 == 12
  └─ (0,460): it is impossible that 10 div 2 == 5
  └─ (0,485): it is impossible that 7 mod 3 == 1
  └─ (0,509): it is impossible that -5 == 0 - 5
  └─ (0,532): it is impossible that notalwaystrue(3, 4)
  └─ (0,605): it is impossible that true ==> true
  └─ (0,632): it is impossible that forall x0 : int f(x0) || !f(x0)
  └─ (0,687): it is impossible that forall x0 : int x0 > 0 || x0 <= 0
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
  (0,103): check f(5) > 1
  └─ (0,110): could not prove f(5) > 1
     under the assumptions
       forall x0 : int f(x0) > 0
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
  (0,138): check f(5) > 10
  └─ (0,145): could not prove f(5) > 10
     under the assumptions
       forall x0 : int f(x0) > 0
       f(1) > 0 && f(4) > 0
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
info: test_reach_bad: ✗ counterexample found
  (0,100): reach f(5) < 0
  └─ (0,106): it is impossible that f(5) < 0
     under the assumptions
       forall x0 : int f(x0) > 0
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
info: test_reach_good: ✗ unknown
  (0,101): reach f(5) > 5
  └─ (0,107): could not prove f(5) > 5
     under the assumptions
       forall x0 : int f(x0) > 0
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
info: test_reach_with_trace: ✗ counterexample found
  (0,137): reach f(5) < 0
  └─ (0,143): it is impossible that f(5) < 0
     under the assumptions
       forall x0 : int f(x0) > 0
       f(1) > 0 && f(4) > 0
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
info: test_reach_diagnosis: ✗ counterexample found
  (0,106): reach f(5) > 5 && f(5) < 0
  └─ (0,112): could not prove f(5) > 5
     under the assumptions
       forall x0 : int f(x0) > 0
  └─ (0,124): it is impossible that f(5) < 0
     under the assumptions
       forall x0 : int f(x0) > 0
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
info: test_all_expressions: ✗ counterexample found
  (0,127): reach (false || true) && (if true true else false) && f(5) && notalwaystrue(1, 2) && 5 == 5 && !(3 == 4) && 2 < 3 && 2 <= 2 && 4 > 3 && 4 >= 4 && 1 + 2 == 4 && 5 - 2 == 3 && 3 * 4 == 12 && 10 div 2 == 5 && 7 mod 3 == 1 && -5 == 0 - 5 && notalwaystrue(3, 4) && (true ==> true) && (forall x0 : int f(x0) || !f(x0)) && (forall x0 : int x0 > 0 || x0 <= 0)
  └─ (0,134): could not prove false || true
  └─ (0,161): could not prove if true true else false
  └─ (0,197): could not prove f(5)
  └─ (0,213): could not prove notalwaystrue(1, 2)
  └─ (0,244): could not prove 5 == 5
  └─ (0,262): could not prove !(3 == 4)
  └─ (0,283): could not prove 2 < 3
  └─ (0,300): could not prove 2 <= 2
  └─ (0,318): could not prove 4 > 3
  └─ (0,335): could not prove 4 >= 4
  └─ (0,353): it is impossible that 1 + 2 == 4
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
info: test_all_expressions: ✗ counterexample found
  (0,85): reach notalwaystrue(1, 2) && !notalwaystrue(1, 2) && 5 == 4
  └─ (0,91): could not prove notalwaystrue(1, 2)
  └─ (0,122): it is impossible that !notalwaystrue(1, 2)
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
