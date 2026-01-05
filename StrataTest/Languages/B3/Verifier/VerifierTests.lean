/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Verifier Tests

Tests for B3 to SMT conversion and verification.

## Implementation Status

**Expressions:**
- ✅ Literals (int, bool, string)
- ✅ Binary operators (==, !=, <, <=, >, >=, +, -, *, div, mod, &&, ||, ==>, <==, <==>)
- ✅ Unary operators (!, -)
- ✅ If-then-else
- ✅ Function calls
- ✅ Quantifiers (forall, exists) with patterns
- ✅ Labeled expressions (labels stripped)
- ✅ Let expressions (variable binding with de Bruijn indices)

**Declarations:**
- ✅ Function declarations
- ✅ Function bodies → quantified axioms
- ✅ Axioms
- ⚠️  Explains clauses (parsed but not used in SMT encoding)
- ❌ Type declarations (not yet encoded to SMT)
- ❌ Tagger declarations (not yet encoded to SMT)
- ❌ Injective parameters → inverse functions (not yet implemented)
- ❌ Tagged functions → tag constants (not yet implemented)
- ✅ When clauses (implemented and tested)

**Statements:**
- ✅ Check (verify property)
- ✅ Assert (verify and assume)
- ✅ Assume (add to solver)
- ✅ Reach (reachability)
- ✅ Block statements
- ❌ Variable declarations (var, val)
- ❌ Assignments
- ❌ Reinit
- ❌ If statements
- ❌ If-case statements
- ❌ Choose statements
- ❌ Loop statements with invariants
- ❌ Labeled statements
- ❌ Exit/Return statements
- ❌ Probe statements
- ❌ Forall statements (aForall)

**Procedures:**
- ✅ Parameter-free procedures
- ❌ Procedures with parameters (in, out, inout)
- ❌ Procedure specifications (requires, ensures)
- ❌ Procedure calls → contract predicates
- ❌ Modular verification

**Verification:**
- ✅ Streaming translation (O(n) not O(n²))
- ✅ Sequential execution (asserts accumulate)
- ✅ Automatic diagnosis (conjunction splitting)
- ✅ Efficient solver reuse (push/pop)
- ✅ Incremental API (init, addFunctionDecl, addAxiom, prove, reach, push, pop)
- ✅ Proper error handling (Except ConversionError)
- ✅ Termination proofs (expressionToSMT is total)
- ❌ When-clause testing in diagnosis (not yet implemented)
- ❌ Definition inlining in diagnosis (not yet implemented)
- ❌ Counterexample parsing and display (not yet implemented)

**Testing:**
- ✅ Unit tests for conversion (ConversionTests.lean)
- ✅ Integration tests with SMT solvers (VerifierTests.lean)
- ❌ Property-based tests with Plausible (future work)
-/

namespace B3.Verifier.Tests

open Strata
open Strata.B3.Verifier

---------------------------------------------------------------------
-- Test Helpers
---------------------------------------------------------------------

def programToB3AST (prog : Program) : B3AST.Program SourceRange :=
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] =>
            match B3CST.Program.ofAst progOp with
            | .ok cstProg =>
                let (ast, _) := B3.programFromCST B3.FromCSTContext.empty cstProg
                ast
            | .error _ => default
        | _ => default
      else default
  | _ => default

def testSMTGeneration (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let commands ← programToSMTCommands ast
  -- Strip common prefix/suffix for stable tests
  let lines := commands.splitOn "\n"
  let filtered := lines.filter (fun line =>
    !line.startsWith "(set-logic" &&
    !line.startsWith "(set-option" &&
    !line.startsWith "(exit"
  )
  IO.println (String.intercalate "\n" filtered)

def formatSourceLocation (baseOffset : String.Pos.Raw) (sr : SourceRange) : String :=
  let relativePos := sr.start.byteIdx - baseOffset.byteIdx
  s!"(0,{relativePos})"

def formatStatementError (prog : Program) (stmt : B3AST.Statement SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := match stmt with
    | .check m _ => formatSourceLocation baseOffset m
    | .assert m _ => formatSourceLocation baseOffset m
    | .assume m _ => formatSourceLocation baseOffset m
    | .reach m _ => formatSourceLocation baseOffset m
    | _ => "unknown location"

  let (cstStmt, _errors) := B3.stmtToCST B3.ToCSTContext.empty stmt
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let state : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  let stmtAst := cstStmt.toAst
  let formatted := (mformat (ArgF.op stmtAst) ctx state).format.pretty.trim

  s!"{loc}: {formatted}"

def formatExpressionError (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := match expr with
    | .binaryOp m _ _ _ => formatSourceLocation baseOffset m
    | .literal m _ => formatSourceLocation baseOffset m
    | .id m _ => formatSourceLocation baseOffset m
    | .ite m _ _ _ => formatSourceLocation baseOffset m
    | .unaryOp m _ _ => formatSourceLocation baseOffset m
    | .functionCall m _ _ => formatSourceLocation baseOffset m
    | .labeledExpr m _ _ => formatSourceLocation baseOffset m
    | .letExpr m _ _ _ => formatSourceLocation baseOffset m
    | .quantifierExpr m _ _ _ _ _ => formatSourceLocation baseOffset m

  let (cstExpr, _) := B3.expressionToCST B3.ToCSTContext.empty expr
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  let formatted := (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trim

  s!"{loc}: {formatted}"

def testVerification (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let reports ← verifyWithDiagnosis ast
  IO.println "Verification results:"
  for report in reports do
    for (result, diagnosis) in report.results do
      match result.decl with
      | .procedure _ name _ _ _ =>
          let marker := if result.result.isError then "✗" else "✓"
          let description := match result.result with
            | .proofResult .proved => "verified"
            | .proofResult .counterexample => "counterexample found"
            | .proofResult .proofUnknown => "proof unknown"
            | .reachabilityResult .unreachable => "unreachable"
            | .reachabilityResult .reachable => "satisfiable"
            | .reachabilityResult .reachabilityUnknown => "reachability unknown"

          IO.println s!"  {name.val}: {marker} {description}"
          if result.result.isError then
            match result.sourceStmt with
            | some stmt =>
                IO.println s!"    {formatStatementError prog stmt}"
            | none => pure ()
            match diagnosis with
            | some diag =>
                if !diag.diagnosedFailures.isEmpty then
                  for (_desc, failedExpr, _) in diag.diagnosedFailures do
                    IO.println s!"    Related: {formatExpressionError prog failedExpr}"
            | none => pure ()
      | _ => pure ()

---------------------------------------------------------------------
-- SMT Generation Tests
---------------------------------------------------------------------

/--
info: (declare-fun abs (Int) Int)
(assert (forall ((x Int)) (! (= (abs x) (ite (>= x 0) x (- x))) :pattern ((abs x)))))
(push 1)
(assert (not (= (abs (- 5)) 5)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function abs(x : int) : int {
  if x >= 0 then x else -x
}
procedure test() {
  check abs(-5) == 5
}
#end

/--
info: (declare-fun isEven (Int) Int)
(declare-fun isOdd (Int) Int)
(assert (forall ((n Int)) (! (= (isEven n) (ite (= n 0) 1 (isOdd (- n 1)))) :pattern ((isEven n)))))
(assert (forall ((n Int)) (! (= (isOdd n) (ite (= n 0) 0 (isEven (- n 1)))) :pattern ((isOdd n)))))
(push 1)
(assert (not (= (isEven 4) 1)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function isEven(n : int) : int {
  if n == 0 then 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 then 0 else isEven(n - 1)
}
procedure test() {
  check isEven(4) == 1
}
#end

/--
info: (declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (=> (> x 0) (> (f x) 0)) :pattern ((f x)))))
(push 1)
(assert (not (=> (> 5 0) (> (f 5) 0))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

---------------------------------------------------------------------
-- Solver Integration Tests
---------------------------------------------------------------------

/--
info: Verification results:
  test: ✓ verified
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
info: Verification results:
  test_fail: ✗ counterexample found
    (0,52): check 5 == 5 && f(5) == 10
    Related: (0,68): f(5) == 10
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end

---------------------------------------------------------------------
-- Reach Tests
---------------------------------------------------------------------

/--
info: Verification results:
  test_reach_bad: ✗ unreachable
    (0,100): reach f(5) < 0
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
info: Verification results:
  test_reach_good: ✓ satisfiable
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
info: Verification results:
  test_reach_diagnosis: ✗ unreachable
    (0,106): reach f(5) > 5 && f(5) < 0
    Related: (0,124): f(5) < 0
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
info: Verification results:
  test_assert_helps: ✓ verified
  test_assert_helps: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_assert_helps() {
  assert f(5) > 0
  check f(5) > -1
}
#end


---------------------------------------------------------------------
-- Expression Coverage Test
---------------------------------------------------------------------

/--
info: (declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))
(push 1)
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= 5 5) (not (= 3 4))) (< 2 3)) (<= 2 2)) (> 4 3)) (>= 4 4)) (+ 1 2)) (- 5 2)) (* 3 4)) (div 10 2)) (mod 7 3)) (- 5)) (=> true true)) (or false true)) (ite true 1 0)) (f 5)) (g 1 2)) (forall ((y Int)) (! (> y 0) :pattern (y))))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : int { x + 1 }
function g(a : int, b : int) : int
procedure test_all_expressions() {
  check 5 == 5 &&
        !(3 == 4) &&
        2 < 3 &&
        2 <= 2 &&
        4 > 3 &&
        4 >= 4 &&
        1 + 2 &&
        5 - 2 &&
        3 * 4 &&
        10 div 2 &&
        7 mod 3 &&
        -5 &&
        (true ==> true) &&
        (false || true) &&
        (if true then 1 else 0) &&
        f(5) &&
        g(1, 2) &&
        (forall y : int y > 0)
}
#end

end B3.Verifier.Tests
