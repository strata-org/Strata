/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Unit tests for `pushOldInward`. Builds StmtExpr AST nodes directly (since
`old(...)` has no Laurel surface syntax) and asserts the rewritten shape and
emitted diagnostics.
-/

import Strata.Languages.Laurel.PushOldInward
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

namespace Strata.Laurel

private def mk (e : StmtExpr) : StmtExprMd := ⟨e, none⟩
private def localVar (name : String) : StmtExprMd := mk (.Var (.Local { text := name }))
private def fieldAccess (obj : StmtExprMd) (field : String) : StmtExprMd :=
  mk (.Var (.Field obj { text := field }))
private def litInt (n : Int) : StmtExprMd := mk (.LiteralInt n)
private def litBool (b : Bool) : StmtExprMd := mk (.LiteralBool b)
private def add (a b : StmtExprMd) : StmtExprMd := mk (.PrimitiveOp .Add [a, b])
private def eqOp (a b : StmtExprMd) : StmtExprMd := mk (.PrimitiveOp .Eq [a, b])
private def call (callee : String) (args : List StmtExprMd) : StmtExprMd :=
  mk (.StaticCall { text := callee } args)
private def old (e : StmtExprMd) : StmtExprMd := mk (.Old e)
private def intTy : AstNode HighType := ⟨ .TInt, none ⟩

/-- Run `pushOldInwardExpr` and return `(rewritten, warningCount)`. -/
private def runPush (inout : List String) (expr : StmtExprMd) : StmtExprMd × Nat :=
  let (out, st) := (pushOldInwardExpr expr).run { inoutNames := inout }
  (out, st.diagnostics.length)

private def fmt (expr : StmtExprMd) : String :=
  toString (Std.Format.pretty (Std.ToFormat.format expr))

private def report (label : String) (inout : List String) (input : StmtExprMd) : IO Unit := do
  let (out, warns) := runPush inout input
  IO.println s!"{label}: {fmt out} warnings={warns}"

/-! ## Leaf cases -/

/--
info: inoutVar: old(h) warnings=0
-/
#guard_msgs in
#eval report "inoutVar" ["h"] (old (localVar "h"))

/--
info: nonInout: x warnings=1
-/
#guard_msgs in
#eval report "nonInout" ["h"] (old (localVar "x"))

/--
info: literal: 42 warnings=1
-/
#guard_msgs in
#eval report "literal" ["h"] (old (litInt 42))

/--
info: bareVar: h warnings=0
-/
#guard_msgs in
#eval report "bareVar" ["h"] (localVar "h")

/-! ## Distribution over operators -/

/--
info: distribute: x + old(h) warnings=0
-/
#guard_msgs in
#eval report "distribute" ["h"] (old (add (localVar "x") (localVar "h")))

/--
info: bothInout: old(a) + old(b) warnings=0
-/
#guard_msgs in
#eval report "bothInout" ["a", "b"] (old (add (localVar "a") (localVar "b")))

/--
info: nestedAdd: x + old(h) + old(k) warnings=0
-/
#guard_msgs in
#eval report "nestedAdd" ["h", "k"]
  (old (add (add (localVar "x") (localVar "h")) (localVar "k")))

/--
info: eq: old(h) == y warnings=0
-/
#guard_msgs in
#eval report "eq" ["h"] (old (eqOp (localVar "h") (localVar "y")))

/-! ## Calls -/

/--
info: staticCall: f(old(h), x) warnings=0
-/
#guard_msgs in
#eval report "staticCall" ["h"] (old (call "f" [localVar "h", localVar "x"]))

/--
info: callNoInout: f(x, y) warnings=1
-/
#guard_msgs in
#eval report "callNoInout" ["h"] (old (call "f" [localVar "x", localVar "y"]))

/-! ## Conditionals -/

/--
info: iteWithInout: if b then old(h) else x warnings=0
-/
#guard_msgs in
#eval report "iteWithInout" ["h"]
  (old (mk (.IfThenElse (localVar "b") (localVar "h") (some (localVar "x")))))

/--
info: iteNoElse: if b then old(h) warnings=0
-/
#guard_msgs in
#eval report "iteNoElse" ["h"]
  (old (mk (.IfThenElse (localVar "b") (localVar "h") none)))

/-! ## Idempotence and nesting -/

/--
info: nested: old(h) warnings=0
-/
#guard_msgs in
#eval report "nested" ["h"] (old (old (localVar "h")))

/--
info: tripleNested: old(h) warnings=0
-/
#guard_msgs in
#eval report "tripleNested" ["h"] (old (old (old (localVar "h"))))

/-! ## Field access (mentionsAnyInout descends into target) -/

/--
info: fieldOnInout: old(h)#field warnings=0
-/
#guard_msgs in
#eval report "fieldOnInout" ["h"] (old (fieldAccess (localVar "h") "field"))

/--
info: fieldOnNonInout: x#field warnings=1
-/
#guard_msgs in
#eval report "fieldOnNonInout" ["h"] (old (fieldAccess (localVar "x") "field"))

/-! ## Old in a sub-expression (top-down rewrite path) -/

/--
info: oldInSubexpr: x + old(h) warnings=0
-/
#guard_msgs in
#eval report "oldInSubexpr" ["h"]
  (add (localVar "x") (old (localVar "h")))

/--
info: oldInCallArg: f(x, old(h)) warnings=0
-/
#guard_msgs in
#eval report "oldInCallArg" ["h"]
  (call "f" [localVar "x", old (localVar "h")])

/-! ## Quantifier body -/

/--
info: quantifier: forall(i: int) => old(h) == i warnings=0
-/
#guard_msgs in
#eval report "quantifier" ["h"]
  (mk (.Quantifier .Forall ⟨{ text := "i" }, intTy⟩ none
        (old (eqOp (localVar "h") (localVar "i")))))

/-! ## Tricky cases -/

-- Outer Old wraps an expression containing an inner Old.
/--
info: oldOfOldPlus: x + old(h) warnings=0
-/
#guard_msgs in
#eval report "oldOfOldPlus" ["h"]
  (old (add (localVar "x") (old (localVar "h"))))

-- Chained field access on an inout root.
/--
info: chainedField: (old(a)#b)#c warnings=0
-/
#guard_msgs in
#eval report "chainedField" ["a"]
  (old (fieldAccess (fieldAccess (localVar "a") "b") "c"))

-- Old of a ReferenceEquals: distributes to both sides.
/--
info: refEq: old(a) == b warnings=0
-/
#guard_msgs in
#eval report "refEq" ["a"]
  (old (mk (.ReferenceEquals (localVar "a") (localVar "b"))))

-- Empty inoutNames: every Old wrapper warns and unwraps.
/--
info: emptyInout: x warnings=1
-/
#guard_msgs in
#eval report "emptyInout" [] (old (localVar "x"))

-- Multiple Olds in the same expression: each is independently processed.
/--
info: twoOlds: old(h) + (old(k) + x) warnings=0
-/
#guard_msgs in
#eval report "twoOlds" ["h", "k"]
  (add (old (localVar "h")) (add (old (localVar "k")) (localVar "x")))

-- Old wrapping an expression composed of inout vars: distributes everywhere.
/--
info: oldOfEqInout: old(a) == old(b) warnings=0
-/
#guard_msgs in
#eval report "oldOfEqInout" ["a", "b"]
  (old (eqOp (localVar "a") (localVar "b")))

-- Quantifier whose body has both an Old(inout) and a non-inout reference.
/--
info: quantBoth: exists(j: int) => old(h) + j == y warnings=0
-/
#guard_msgs in
#eval report "quantBoth" ["h"]
  (mk (.Quantifier .Exists ⟨{ text := "j" }, intTy⟩ none
        (eqOp (add (old (localVar "h")) (localVar "j")) (localVar "y"))))

-- Bool literal under Old: warns and unwraps regardless of inout context.
/--
info: oldOfBool: true warnings=1
-/
#guard_msgs in
#eval report "oldOfBool" ["h"] (old (litBool true))

-- Old of a PrimitiveOp where one arg is already old(inout): collapses fine.
/--
info: redundantInner: old(h) + old(k) warnings=0
-/
#guard_msgs in
#eval report "redundantInner" ["h", "k"]
  (old (add (old (localVar "h")) (localVar "k")))

-- Field path where only an inner segment is inout.
/--
info: fieldOnInnerInout: f(a, old(h))#field warnings=0
-/
#guard_msgs in
#eval report "fieldOnInnerInout" ["h"]
  (old (fieldAccess (call "f" [localVar "a", localVar "h"]) "field"))

/-! ## Stress cases -/

-- Quantifier param shadows an inout name. The body's reference to `h`
-- *should* still be rewritten to old(h) because shadowing is a scoping
-- concern that pushOld does not currently track. This documents the
-- current behavior so any future shadow handling is intentional.
/--
info: shadowingQuantifier: forall(h: int) => old(h) + 1 warnings=0
-/
#guard_msgs in
#eval report "shadowingQuantifier" ["h"]
  (mk (.Quantifier .Forall ⟨{ text := "h" }, intTy⟩ none
        (old (add (localVar "h") (litInt 1)))))

-- Old whose argument is a primitive op of two literals: no inout, warn.
/--
info: oldOfLitOp: 1 + 2 warnings=1
-/
#guard_msgs in
#eval report "oldOfLitOp" ["h"] (old (add (litInt 1) (litInt 2)))

-- Mix of nested Old and non-Old subexpressions in a call's args.
/--
info: callMixedOld: g(old(h), old(k), x, y) warnings=0
-/
#guard_msgs in
#eval report "callMixedOld" ["h", "k"]
  (call "g" [old (localVar "h"), old (localVar "k"), localVar "x", localVar "y"])

-- ITE wrapped in Old where only the condition contains an inout: distributes.
/--
info: iteCondInout: if old(h) then 1 else 2 warnings=0
-/
#guard_msgs in
#eval report "iteCondInout" ["h"]
  (old (mk (.IfThenElse (localVar "h") (litInt 1) (some (litInt 2)))))

-- Reference equality with inout on both sides + a deeply nested old.
/--
info: deepRefEq: old(a) == f(old(b), old(b)) warnings=0
-/
#guard_msgs in
#eval report "deepRefEq" ["a", "b"]
  (old (mk (.ReferenceEquals (localVar "a") (call "f" [localVar "b", old (localVar "b")]))))

-- Old over a quantifier whose body uses the bound variable. The bound variable
-- is not inout, so it stays as is; the inout `h` referenced in the body is
-- rewritten.
/--
info: oldOverQuant: forall(i: int) => old(h) > i warnings=0
-/
#guard_msgs in
#eval report "oldOverQuant" ["h"]
  (old (mk (.Quantifier .Forall ⟨{ text := "i" }, intTy⟩ none
        (mk (.PrimitiveOp .Gt [localVar "h", localVar "i"])))))

-- Old wrapping a call whose only argument is itself an old(inout).
-- Top-down, the inner old is processed first, then the outer distributes.
/--
info: oldOverOldArg: f(old(h)) warnings=0
-/
#guard_msgs in
#eval report "oldOverOldArg" ["h"] (old (call "f" [old (localVar "h")]))

-- Empty inout list and an expression with no Old: passthrough, no warnings.
/--
info: noOpExpr: a + b + c warnings=0
-/
#guard_msgs in
#eval report "noOpExpr" []
  (add (add (localVar "a") (localVar "b")) (localVar "c"))

-- Old wrapping a Field where the inout is the field's owner (chain on inout).
/--
info: oldFieldInout: old(h)#count warnings=0
-/
#guard_msgs in
#eval report "oldFieldInout" ["h"] (old (fieldAccess (localVar "h") "count"))

-- Multiple non-inout Olds in the same expression each warn independently.
/--
info: twoBadOlds: x + y warnings=2
-/
#guard_msgs in
#eval report "twoBadOlds" ["h"]
  (add (old (localVar "x")) (old (localVar "y")))

/-! ## Edge cases on the public surface -/

-- pushOld direct invocation: confirms the helper, when called on an
-- inout var, wraps it in Old (used internally when Old(inout) is at root).
private def runPushOldOnly (inout : List String) (expr : StmtExprMd) : StmtExprMd × Nat :=
  let (out, st) := (pushOld expr).run { inoutNames := inout }
  (out, st.diagnostics.length)

private def reportPushOld (label : String) (inout : List String) (input : StmtExprMd) : IO Unit := do
  let (out, warns) := runPushOldOnly inout input
  IO.println s!"{label}: {fmt out} warnings={warns}"

-- pushOld on a bare inout var directly emits old(h).
/--
info: pushOldOnVar: old(h) warnings=0
-/
#guard_msgs in
#eval reportPushOld "pushOldOnVar" ["h"] (localVar "h")

-- pushOld on a non-inout var passes through (no Old wrapper, no warning;
-- the warning is the responsibility of pushOldInwardExpr's outer check).
/--
info: pushOldOnNonInout: x warnings=0
-/
#guard_msgs in
#eval reportPushOld "pushOldOnNonInout" ["h"] (localVar "x")

-- mentionsAnyInout direct: confirms it descends into nested structure.
/--
info: true
-/
#guard_msgs in
#eval mentionsAnyInout ["h"]
  (call "f" [add (litInt 1) (fieldAccess (localVar "h") "x")])

/--
info: false
-/
#guard_msgs in
#eval mentionsAnyInout ["h"] (add (localVar "a") (litInt 0))

-- An assignment LHS field target shouldn't be reached by pushOldInwardExpr
-- via a top-level `Old`, but if an `Old` happens to wrap an `Assign`'s value
-- expression we should still produce something sensible. Synthetic check:
-- old wrapping a deeply nested call whose root contains the inout.
/--
info: deepCall: f(g(h(old(a)), x), 7) warnings=0
-/
#guard_msgs in
#eval report "deepCall" ["a"]
  (call "f" [call "g" [call "h" [old (localVar "a")], localVar "x"], litInt 7])

/-! ## Pathological cases -/

-- Old over a quantifier whose trigger references inout: trigger and body
-- both get the Old distributed.
/--
info: quantWithTrigger: forall(i: int){old(h)} => old(h) > i warnings=0
-/
#guard_msgs in
#eval report "quantWithTrigger" ["h"]
  (old (mk (.Quantifier .Forall ⟨{ text := "i" }, intTy⟩
            (some (localVar "h"))
            (mk (.PrimitiveOp .Gt [localVar "h", localVar "i"])))))

-- Empty call with no args + inout context: distributes trivially over zero args,
-- the result still has no inout reference, so it warns.
/--
info: emptyCall: f() warnings=1
-/
#guard_msgs in
#eval report "emptyCall" ["h"] (old (call "f" []))

-- Top-down: an Old buried under a Quantifier (not the quantifier itself).
/--
info: oldUnderQuant: forall(i: int) => old(h) + i == 0 warnings=0
-/
#guard_msgs in
#eval report "oldUnderQuant" ["h"]
  (mk (.Quantifier .Forall ⟨{ text := "i" }, intTy⟩ none
        (eqOp (add (old (localVar "h")) (localVar "i")) (litInt 0))))

-- Two layers of quantifiers, Old in the inner body referencing the outer-bound
-- variable (which is not inout) plus an actual inout.
/--
info: nestedQuant: forall(i: int) => exists(j: int) => old(h) + i + j == 0 warnings=0
-/
#guard_msgs in
#eval report "nestedQuant" ["h"]
  (mk (.Quantifier .Forall ⟨{ text := "i" }, intTy⟩ none
        (mk (.Quantifier .Exists ⟨{ text := "j" }, intTy⟩ none
              (eqOp (add (add (old (localVar "h")) (localVar "i"))
                          (localVar "j"))
                    (litInt 0))))))

-- Old on the field itself when the chain mixes inout and non-inout.
-- old(x.h.field): the variable here is `x` (non-inout, treated as the root),
-- so the wrapper warns and unwraps; the `h` segment is just a field name,
-- not a Var reference, so it stays untouched.
/--
info: mixedFieldChain: (x#h)#field warnings=1
-/
#guard_msgs in
#eval report "mixedFieldChain" ["h"]
  (old (fieldAccess (fieldAccess (localVar "x") "h") "field"))

end Strata.Laurel
