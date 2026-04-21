/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier

/-! ## Tests for let bindings in Core expressions

Let bindings `let v : T := e in body` are desugared to lambda application
`(λ v : T. body) e` in the internal representation. These tests cover:
- SMT encoding (inlining via substitution)
- AST → CST pretty-printing (detecting the lambda application pattern)
- End-to-end verification
-/

namespace Core.LetBindingTests

open Lambda
open Strata.SMT

/-! ### SMT Encoder: let expressions are inlined via substitution -/

-- Let with free variable in body: (λ v : int. v == x) 3 → 3 == x
/--
info: "; x\n(declare-const x Int)\n(define-fun $__t.0 () Int x)\n(define-fun $__t.1 () Bool (= 3 $__t.0))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app ()
    (.abs () "" (.some .int)
      (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))
    (.intConst () 3))

-- Let substituting a free var for the bound var: (λ v. v == x) y → y == x
/--
info: "; y\n(declare-const y Int)\n(define-fun $__t.0 () Int y)\n; x\n(declare-const x Int)\n(define-fun $__t.1 () Int x)\n(define-fun $__t.2 () Bool (= $__t.0 $__t.1))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app ()
    (.abs () "" (.some .int)
      (.eq () (.bvar () 0) (.fvar () "x" (.some .int))))
    (.fvar () "y" (.some .int)))

-- Nested let with free vars: (λ a. (λ b. a == b) y) x → x == y
/--
info: "; x\n(declare-const x Int)\n(define-fun $__t.0 () Int x)\n; y\n(declare-const y Int)\n(define-fun $__t.1 () Int y)\n(define-fun $__t.2 () Bool (= $__t.0 $__t.1))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app ()
    (.abs () "" (.some .int)
      (.app ()
        (.abs () "" (.some .int)
          (.eq () (.bvar () 1) (.bvar () 0)))
        (.fvar () "y" (.some .int))))
    (.fvar () "x" (.some .int)))

-- Let with ite in body: (λ v. if v then 1 else 0) b
/--
info: "; b\n(declare-const b Bool)\n(define-fun $__t.0 () Bool b)\n(define-fun $__t.1 () Int (ite $__t.0 1 0))\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app ()
    (.abs () "" (.some .bool)
      (.ite () (.bvar () 0) (.intConst () 1) (.intConst () 0)))
    (.fvar () "b" (.some .bool)))

-- Let where body ignores bound var and uses a free var: (λ v. x) 42 → x
/--
info: "; x\n(declare-const x Int)\n(define-fun $__t.0 () Int x)\n"
-/
#guard_msgs in
#eval toSMTTermString
  (.app () (.abs () "" (.some .int) (.fvar () "x" (.some .int))) (.intConst () 42))

/-! ### AST → CST: let expressions pretty-print as `let v : T := e in body` -/

section ASTtoCST

open Strata
open Strata.CoreDDM

def ASTtoCST (program : Strata.Program) := do
  let (ast, errs) := TransM.run Inhabited.default (translateProgram program)
  if !errs.isEmpty then
    IO.println f!"CST to AST Error: {errs}"
  IO.println f!"{Core.formatProgram ast}"

-- Let with constant body
private def testLetConst : Strata.Program :=
#strata
program Core;

procedure LetConst() returns (y : int)
{
  y := let v : int := 5 in 5;
};
#end

/--
info: program Core;

procedure LetConst () returns (y : int)
{
  y := let __q0 : int := 5 in 5;
  };
-/
#guard_msgs in
#eval ASTtoCST testLetConst

-- Let with body referencing procedure parameter
private def testLetRefParam : Strata.Program :=
#strata
program Core;

procedure LetRefParam(x : int) returns (y : int)
{
  y := let v : int := 5 in x;
};
#end

/--
info: program Core;

procedure LetRefParam (x : int) returns (y : int)
{
  y := let __q0 : int := 5 in x;
  };
-/
#guard_msgs in
#eval ASTtoCST testLetRefParam

-- Let with body using the bound variable
private def testLetUseBound : Strata.Program :=
#strata
program Core;

procedure LetUseBound() returns (y : int)
{
  y := let v : int := 5 in v;
};
#end

/--
info: program Core;

procedure LetUseBound () returns (y : int)
{
  y := let __q0 : int := 5 in __q0;
  };
-/
#guard_msgs in
#eval ASTtoCST testLetUseBound

-- Let with boolean type
private def testLetBool : Strata.Program :=
#strata
program Core;

procedure LetBool() returns (y : bool)
{
  y := let v : bool := true in false;
};
#end

/--
info: program Core;

procedure LetBool () returns (y : bool)
{
  y := let __q0 : bool := true in false;
  };
-/
#guard_msgs in
#eval ASTtoCST testLetBool

end ASTtoCST

/-! ### End-to-end verification with let bindings -/

section Verification

-- Verify a let binding with constant value and body
private def testLetVerifyConst : Strata.Program :=
#strata
program Core;

procedure LetConst() returns (y : int)
spec {
  ensures (y == 5);
}
{
  y := let v : int := 5 in 5;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: LetConst_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: LetConst_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.verify testLetVerifyConst

-- Verify a let binding where the body uses the bound variable
private def testLetVerifyBoundVar : Strata.Program :=
#strata
program Core;

procedure LetBoundVar() returns (y : int)
spec {
  ensures (y == 5);
}
{
  y := let v : int := 5 in v;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: LetBoundVar_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: LetBoundVar_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.verify testLetVerifyBoundVar

-- Verify a let binding where the body references a procedure parameter
private def testLetVerifyParam : Strata.Program :=
#strata
program Core;

procedure LetParam(x : int) returns (y : int)
spec {
  ensures (y == x);
}
{
  y := let v : int := 42 in x;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: LetParam_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: LetParam_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.verify testLetVerifyParam

end Verification

end Core.LetBindingTests
