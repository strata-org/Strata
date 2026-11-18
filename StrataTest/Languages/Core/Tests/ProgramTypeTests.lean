/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

def bad_prog : Program := { decls := [
      -- type Foo a b;
      .type (.con { name := "Foo", params := ["a", "b"]}) .empty,
      -- type FooAlias a = Foo a a;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo %a %a]}) .empty,
      -- const fooAliasVal : FooAlias bool;
      .func { name := "fooAliasVal", inputs := [], output := mty[FooAlias bool]} .empty,
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]} .empty,
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := .structured [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)] .empty
              ]
      } .empty
]}

/--
info: error: Procedure 'P': Impossible to unify (Foo bool bool) with (Foo int bool).
First mismatch: bool with int.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default bad_prog
         return (format ans)

def good_prog : Program := { decls := [
      -- type Foo a b;
      .type (.con { name := "Foo", params := ["a", "b"]}) .empty,
      -- type FooAlias a = Foo a bool;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo %a bool]}) .empty,
      -- const fooAliasVal : ∀a. FooAlias a;
      .func { name := "fooAliasVal", typeArgs := ["a"], inputs := [], output := mty[FooAlias %a]}
        .empty,
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]} .empty,
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := .structured [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)] .empty
              ]
      } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: test
Property: assert
Obligation:
fooAliasVal == fooVal

---
info: ok: program Core;

type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo a bool;
function fooAliasVal<a> () : Foo a bool;
function fooVal () : Foo int bool;
procedure P ()
{
  assert [test]: fooAliasVal == fooVal;
};
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default good_prog
         return (format ans)

/-! ## Parametric alias resolution -/

-- `Pair int bool` expands to `Map int bool`, so `p1` and `p2` have the same type.
def paramAliasMatch : Program := { decls := [
      .type (.syn { name := "Pair", typeArgs := ["a", "b"],
                    type := .tcons "Map" [.ftvar "a", .ftvar "b"] }) .empty,
      .func { name := "p1", inputs := [], output := mty[Pair int bool]} .empty,
      .func { name := "p2", inputs := [], output := mty[Map int bool]} .empty,
      .proc { header := {name := "P", typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [
                Statement.assert "test" eb[(~p1 == ~p2)] .empty
              ] } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: test
Property: assert
Obligation:
p1 == p2

---
info: ok: program Core;

type Pair (a : Type, b : Type) := Map a b;
function p1 () : Map int bool;
function p2 () : Map int bool;
procedure P ()
{
  assert [test]: p1 == p2;
};
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default paramAliasMatch
         return (format ans)

-- `Pair int bool` expands to `Map int bool`, which cannot unify with `Map bool int`.
def paramAliasMismatch : Program := { decls := [
      .type (.syn { name := "Pair", typeArgs := ["a", "b"],
                    type := .tcons "Map" [.ftvar "a", .ftvar "b"] }) .empty,
      .func { name := "p1", inputs := [], output := mty[Pair int bool]} .empty,
      .func { name := "p2", inputs := [], output := mty[Map bool int]} .empty,
      .proc { header := {name := "P", typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [
                Statement.assert "test" eb[(~p1 == ~p2)] .empty
              ] } .empty
]}

/--
info: error: Procedure 'P': Impossible to unify (Map int bool) with (Map bool int).
First mismatch: int with bool.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default paramAliasMismatch
         return (format ans)

---------------------------------------------------------------------

def outOfScopeVarProg : Program := { decls := [
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [("x", mty[bool])],
                         outputs := [("y", mty[bool])] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := .structured [
                Statement.set "y" eb[((~Bool.Or x) x)] .empty,
                .ite (.det eb[(x == #true)])
                  [Statement.init "q" t[int] (.det eb[#0]) .empty,
                           Statement.set "q" eb[#1] .empty,
                           Statement.set "y" eb[#true] .empty]
                  [Statement.init "q" t[int] (.det eb[#0]) .empty,
                           Statement.set "q" eb[#2] .empty,
                           Statement.set "y" eb[#true] .empty]
                  .empty,
                Statement.assert "y_check" eb[y == #true] .empty,
                Statement.assert "q_check" eb[q == #1] .empty
              ]
      } .empty
]}

/--
info: error: Procedure 'P': [assert [q_check] (q == #1)] No free variables are allowed here!
Free Variables: [q]
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default outOfScopeVarProg
         return (format ans)

/-- A procedure whose body is the single assertion `e`. -/
private def assertProg (e : Expression.Expr) : Program :=
  { decls := [.proc { header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured [Statement.assert "a" e .empty] } .empty] }

-- An unbound variable is reported before a type error to its left.
/--
info: REJECTED: Procedure 'P': [assert [a] ((#1 == #true) == x)] No free variables are allowed here!
Free Variables: [x]
-/
#guard_msgs in
#eval Core.TestUtil.programVerdict (assertProg
  (.eq Core.coreLoc (.eq Core.coreLoc (.intConst Core.coreLoc 1) (.boolConst Core.coreLoc true))
    (.fvar Core.coreLoc ⟨"x", ()⟩ none)))

-- A free variable named like the generated binder is reported as unbound.
/--
info: REJECTED: Procedure 'P': [assert [a] (∀ (bvar:int) ($__var0 == %0))] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval Core.TestUtil.programVerdict (assertProg (Core.TestUtil.allOf (some .int)
  (.eq Core.coreLoc Core.TestUtil.generatedBinderOccurrence (.bvar Core.coreLoc 0))))

---------------------------------------------------------------------

def polyFuncProg : Program := { decls := [
  -- function identity<a>(x : a) : a;
  .func { name := "identity",
          typeArgs := ["a"],
          inputs := [("x", .ftvar "a")],
          output := .ftvar "a" } .empty,
  -- function makePair<a, b>(x : a, y : b) : Map a b;
  .func { name := "makePair",
          typeArgs := ["a", "b"],
          inputs := [("x", .ftvar "a"), ("y", .ftvar "b")],
          output := .tcons "Map" [.ftvar "a", .ftvar "b"] } .empty,
  -- procedure Test()
  .proc { header := { name := "Test",
                      typeArgs := [],
                      inputs := [],
                      outputs := [] },
          spec := { preconditions := [],
                    postconditions := [] },
          body := .structured [
            -- var m : Map int bool;
            Statement.init "m" (.forAll [] (.tcons "Map" [.tcons "int" [], .tcons "bool" []])) Imperative.ExprOrNondet.nondet .empty,
            -- m := makePair(identity(42), identity(true));
            Statement.set "m" eb[((~makePair (~identity #42)) (~identity #true))] .empty
          ]
  } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function identity<a> (x : a) : a;
function makePair<a, b> (x : a, y : b) : Map a b;
procedure Test ()
{
  var m : (Map int bool);
  m := makePair(identity(42), identity(true));
};
-/
#guard_msgs in
#eval do
  let ans ← typeCheck .default polyFuncProg
  return (format ans)


section
def intIdentityFnPgm : Program := { decls := [
  .func { name := "intID",
          typeArgs := [],
          inputs := [],
          output := .arrow .int .int,
          body := some eb[λ %0]
          } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info: ok: program Core;

function intID () : int -> int {
  fun __q0 : int => __q0
}
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default intIdentityFnPgm
          return (format ans)
end

---------------------------------------------------------------------

/-- `lemma [l] <a>: forall y : a, z : a :: y == z`. -/
def polymorphicLemmaPgm : Program := { decls := [
  .lemma { name := "l", typeArgs := ["a"],
           e := .quant Core.coreLoc .all "y" (some (.ftvar "a"))
                  (Lambda.LExpr.noTrigger Core.coreLoc)
                  (.quant Core.coreLoc .all "z" (some (.ftvar "a"))
                    (Lambda.LExpr.noTrigger Core.coreLoc)
                    (.eq Core.coreLoc (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 0))) } .empty
]}

-- The obligation program states the lemma as an assertion.
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: l
Property: assert
Obligation:
y@1 == z@1

---
info: ok: program Core;

procedure l ()
{
  assert [l]: y@1 == z@1;
};
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default polymorphicLemmaPgm
          return (format ans)

-- The checked program keeps the lemma's type parameter `a`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: [("l", ["a"])]
-/
#guard_msgs in
#eval match Core.typeCheck .default polymorphicLemmaPgm with
  | .ok p => p.decls.filterMap (fun | Decl.lemma l _ => some (l.name, l.typeArgs) | _ => none)
  | .error _ => []

---------------------------------------------------------------------

/-- A `Decl.func` with `isRecursive := true` should be rejected.
    `Decl.func` is for non-recursive functions only; recursive functions
    must use `Decl.recFuncBlock`. -/
def recursiveFuncDeclProg : Program := { decls := [
  .func { name := "bad", isRecursive := true, inputs := [("x", .int)], output := .int } .empty
]}

/--
info: error: Decl.func does not allow recursive functions. Use recFuncBlock instead: 'bad'
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default recursiveFuncDeclProg
         return (format ans)

/-- `datatype D { C(x : int) }`: its constructor `C` is a function of the program. -/
private def constrCDatatype : Decl :=
  .type (.data [{ name := "D", typeArgs := [],
                  constrs := [{ name := ⟨"C", ()⟩, args := [(⟨"x", ()⟩, .int)],
                                testerName := "D..isC" }],
                  constrs_ne := rfl }]) .empty

-- A function, or a recursive block member, named like the constructor `C` is rejected.
/--
info: REJECTED: Error in function C: a function of this name already exists.
REJECTED: Error in function C: a function of this name already exists.
-/
#guard_msgs in
#eval Core.TestUtil.printEach [
  Core.TestUtil.programVerdict { decls := [constrCDatatype,
    .func { name := "C", inputs := [("x", .int)], output := .tcons "D" [] } .empty] },
  Core.TestUtil.programVerdict { decls := [constrCDatatype,
    .recFuncBlock [{ name := "C", isRecursive := true, inputs := [("x", .int)],
                     output := .tcons "D" [] }] .empty] }]

/-- `MyUnit`, whose constructor `MkU` generates the tester `isMkU`. -/
private def unitDatatype : Lambda.LDatatype Unit :=
  { name := "MyUnit", typeArgs := [],
    constrs := [{ name := "MkU", args := [] }], constrs_ne := rfl }

/-- A function may not reuse the name of a datatype's generated tester. -/
private def testerNameFuncProg : Program := { decls := [
  .type (.data [unitDatatype]) .empty,
  .func { name := "isMkU", inputs := [("x", .int)], output := .bool } .empty
]}

/--
info: error: Error in function isMkU: a function of this name already exists.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default testerNameFuncProg
         return (format ans)

/-- No function of a recursive block may reuse a factory function's name. -/
private def builtinNameRecBlockProg : Program := { decls := [
  .recFuncBlock [
    { name := "f", isRecursive := true, inputs := [("x", .int)],
      output := .int },
    { name := "Int.Add", isRecursive := true, inputs := [("x", .int)],
      output := .int }] .empty
]}

/--
info: error: Error in function Int.Add: a function of this name already exists.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default builtinNameRecBlockProg
         return (format ans)

/-! ## Rigid type names in expression annotations -/

-- A precondition annotation naming a type with the rigid prefix is rejected.
private def rigidAnnotationPreconditionPgm : Program := { decls := [
  .proc { header := { name := "P", typeArgs := ["a"],
                      inputs := [("x", .ftvar "a")], outputs := [] },
          spec := { preconditions := [("req",
                      ⟨.eq Core.coreLoc (.fvar Core.coreLoc "x" (some (.tcons "$__rigid_a" [])))
                              (.fvar Core.coreLoc "x" (some (.tcons "$__rigid_a" []))), .Default,
                                  #[]⟩)],
                    postconditions := [] } } .empty
]}

/--
info: error: Procedure 'P', condition 'req': Type $__rigid_a is not an instance of a previously registered type!
-/
#guard_msgs (whitespace := lax) in
#eval Core.TestUtil.firstLineOf
  (Std.format (Core.typeCheck .default rigidAnnotationPreconditionPgm))

-- An annotation inside a procedure body naming a type with the rigid prefix is rejected.
private def rigidAnnotationBodyPgm : Program := { decls := [
  .proc { header := { name := "P", typeArgs := ["a"],
                      inputs := [("x", .ftvar "a")], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            Statement.assert "eq"
              (.eq Core.coreLoc (.fvar Core.coreLoc "x" (some (.tcons "$__rigid_a" [])))
                      (.fvar Core.coreLoc "x" (some (.tcons "$__rigid_a" [])))) .empty
          ] } .empty
]}

/-- info: error: Procedure 'P': Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs (whitespace := lax) in
#eval Core.TestUtil.firstLineOf (Std.format (Core.typeCheck .default rigidAnnotationBodyPgm))

-- An ordinary type annotation is accepted.
private def ordinaryAnnotationPgm : Program := { decls := [
  .proc { header := { name := "P", typeArgs := [],
                      inputs := [("x", mty[int])], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            Statement.assert "eq"
              (.eq Core.coreLoc (.fvar Core.coreLoc "x" (some mty[int]))
                (.fvar Core.coreLoc "x" (some mty[int]))) .empty
          ] } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (x : int)
{
  assert [eq]: x == x;
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default ordinaryAnnotationPgm)

-- A variable named with the non-reserved prefix `$__liftfncl` is accepted.
private def transformPrefixVarNamePgm : Program := { decls := [
  .proc { header := { name := "P", typeArgs := [],
                      inputs := [("$__liftfncl_x", mty[int])], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            Statement.assert "eq"
              (.eq Core.coreLoc (.fvar Core.coreLoc "$__liftfncl_x" (some mty[int]))
                      (.fvar Core.coreLoc "$__liftfncl_x" (some mty[int]))) .empty
          ] } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P ($__liftfncl_x : int)
{
  assert [eq]: $__liftfncl_x == $__liftfncl_x;
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default transformPrefixVarNamePgm)

/-! ## Body-local type names -/

-- A body-local type may not reuse the name of a later program-level synonym.
private def bodyLocalTypeShadowsLaterSynonymPgm : Program := { decls := [
  .proc { header := { name := "caller", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "MyInt", params := [] } .empty,
            Statement.init "x" (.forAll [] (.tcons "MyInt" [])) .nondet .empty,
            .cmd (.call "callee" [.inArg (.fvar Core.coreLoc "x" none)] .empty)
          ] } .empty,
  .type (.syn { name := "MyInt", typeArgs := [], type := mty[int] }) .empty,
  .proc { header := { name := "callee", typeArgs := [],
                      inputs := [("y", .tcons "MyInt" [])], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [] } .empty
]}

/--
info: error: Procedure 'caller': Type 'MyInt' is already declared at the program level
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalTypeShadowsLaterSynonymPgm)

-- A body-local type may not reuse the name of an earlier program-level synonym.
private def bodyLocalTypeShadowsEarlierSynonymPgm : Program := { decls := [
  .type (.syn { name := "MyInt", typeArgs := [], type := mty[int] }) .empty,
  .proc { header := { name := "caller", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "MyInt", params := [] } .empty
          ] } .empty
]}

/--
info: error: Procedure 'caller': Type 'MyInt' is already declared at the program level
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalTypeShadowsEarlierSynonymPgm)

-- A body-local type is accepted when no program declaration uses its name.
private def bodyLocalTypeFreshNamePgm : Program := { decls := [
  .proc { header := { name := "caller", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "LocalOnly", params := [] } .empty,
            Statement.init "x" (.forAll [] (.tcons "LocalOnly" [])) .nondet .empty
          ] } .empty,
  .type (.syn { name := "MyInt", typeArgs := [], type := mty[int] }) .empty
]}

/-- info: ACCEPTED -/
#guard_msgs in
#eval Core.TestUtil.coreVerdict bodyLocalTypeFreshNamePgm

-- Two sibling blocks may each declare a body-local type of the same name.
private def bodyLocalTypeSiblingBlocksPgm : Program := { decls := [
  .proc { header := { name := "caller", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .block "b1" [ .typeDecl { name := "LocalOnly", params := [] } .empty ] .empty,
            .block "b2" [ .typeDecl { name := "LocalOnly", params := [] } .empty ] .empty
          ] } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure caller ()
{
  b1: {
    type LocalOnly;
  }
  b2: {
    type LocalOnly;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalTypeSiblingBlocksPgm)

---------------------------------------------------------------------

/-- A function may not reuse the name of a built-in function. -/
private def builtinNameFuncProg : Program := { decls := [
  .func { name := "Int.Add", inputs := [("x", .int)], output := .int } .empty
]}

/--
info: error: Error in function Int.Add: a function of this name already exists.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default builtinNameFuncProg
         return (format ans)

---------------------------------------------------------------------

end Tests

/-- The type variables annotating the last stored declaration when it is an axiom or a lemma, or
    `rejected` when checking fails. -/
private def storedTypeVars (program : Program) : List String :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default program with
  | .ok (program, _) =>
    match program.decls.getLast? with
    | some (.ax a _) => (Lambda.annotTyVars a.e).eraseDups
    | some (.lemma l _) => (Lambda.annotTyVars l.e).eraseDups
    | _ => []
  | .error _ => ["rejected"]

/-! ## Axiom type checking -/

namespace AxiomTypeCheckTests

open Lambda
open Core.TestUtil (allOf anyFunction generatedBinderOccurrence printEach programVerdict)

/-- The last declaration's expression after checking, when it is an axiom. -/
private def storedAxiom (program : Program) : Std.Format :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default program with
  | .ok (program, _) =>
    match program.decls.getLast? with
    | some (.ax a _) => (Lambda.LExpr.instToFormatLExpr Core.CoreLParams.mono).format a.e
    | _ => "not an axiom"
  | .error _ => "rejected"

/-- A program containing one axiom. -/
private def axiomProgram (name : String) (e : Expression.Expr) : Program :=
  { decls := [.ax { name := name, e := e } .empty] }

/-- Axiom `A` is a bare `any`, constrained only by the expected axiom type. -/
private def expectedBoolProgram : Program :=
  { decls := [
      .func anyFunction .empty,
      .ax { name := "A", e := .op Core.coreLoc ⟨"any", ()⟩ none } .empty] }

-- An axiom whose free variable has the generated binder's name is rejected.
/--
info: REJECTED: Error in axiom A: [(∀ (bvar:int) ($__var0 == #1))] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval programVerdict (axiomProgram "A"
  (allOf (some .int) (.eq Core.coreLoc generatedBinderOccurrence
                      (.const Core.coreLoc (.intConst 1)))))

-- An axiom whose binder type nothing constrains is rejected.
/-- info: REJECTED: Axiom 'A' is typed at a generated type variable that is not declared -/
#guard_msgs in
#eval programVerdict (axiomProgram "A"
                      (allOf none (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))))

-- An axiom binder typed at type variable `b` is rejected: `b` is not in scope.
/-- info: REJECTED: Error in axiom A: type variable `b` is not in scope -/
#guard_msgs in
#eval programVerdict (axiomProgram "A"
  (allOf (some (.ftvar "b")) (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))))

-- A binder annotation at a type variable not in scope is rejected even if the body fixes it.
/--
info: REJECTED: Error in axiom A: type variable `$__ty999` is not in scope
-/
#guard_msgs in
#eval programVerdict (axiomProgram "A"
    (allOf (some (.ftvar "$__ty999"))
      (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.const Core.coreLoc (.intConst 1)))))

-- Accepted: a reference to the quantifier's own binder, and an omitted binder type the body fixes.
/--
info: ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach [
  programVerdict (axiomProgram "A"
    (allOf (some .int) (.eq Core.coreLoc (.bvar Core.coreLoc 0)
                        (.const Core.coreLoc (.intConst 1))))),
  programVerdict (axiomProgram "A"
                  (allOf none (.eq Core.coreLoc (.bvar Core.coreLoc 0)
                               (.const Core.coreLoc (.intConst 1)))))]

-- A reserved generated name is accepted as an axiom name.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (axiomProgram "$__ty0" (.const Core.coreLoc (.boolConst true)))

-- An annotation naming `$__rigid_a`, a type with the rigid prefix, is rejected.
/--
info: REJECTED: Error in axiom A: Type $__rigid_a is not an instance of a previously registered type!
-/
#guard_msgs in
#eval Core.TestUtil.firstLineOf (programVerdict (axiomProgram "A"
  (allOf (some (.tcons "$__rigid_a" [])) (.const Core.coreLoc (.boolConst true)))))

-- An axiom must have boolean type.
/-- info: REJECTED: Error in axiom A: Impossible to unify int with bool. -/
#guard_msgs in
#eval programVerdict (axiomProgram "A" (.const Core.coreLoc (.intConst 1)))

-- The expected axiom type resolves `any`'s result to bool in the stored axiom.
/-- info: (ACCEPTED, (~any : bool)) -/
#guard_msgs in
#eval (programVerdict expectedBoolProgram, storedAxiom expectedBoolProgram)

end AxiomTypeCheckTests

/-! ## Lemma type checking -/

namespace LemmaTypeCheckTests

open Lambda
open Core.TestUtil (allOf anyFunction printEach programVerdict)

/-- A program containing one lemma. -/
private def lemmaProgram (name : String) (typeArgs : List String) (e : Expression.Expr) :
    Program :=
  { decls := [.lemma { name := name, typeArgs := typeArgs, e := e } .empty] }

/-- `∀ x : ty. x == x`. -/
private def reflAt (ty : LMonoTy) : Expression.Expr :=
  allOf (some ty) (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))

-- A reserved generated name is accepted as a lemma name.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (lemmaProgram "$__ty0" [] (.const Core.coreLoc (.boolConst true)))

-- A lemma listing type parameter `a` twice is rejected.
/-- info: REJECTED: Error in lemma L: duplicate type arguments [a, a] -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["a", "a"] (reflAt (.ftvar "a")))

-- A reserved generated name as a type parameter is renamed, so the lemma is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["$__ty0"] (reflAt (.ftvar "$__ty0")))

-- A binder typed at `b` is rejected when `b` is not a type parameter of the lemma.
/-- info: REJECTED: Error in lemma L: type variable `b` is not in scope -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["a"] (reflAt (.ftvar "b")))

-- A polymorphic lemma whose binder is typed at its type parameter `a` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["a"] (reflAt (.ftvar "a")))

/-- The lemma `L<a>: ∀ x : a. x == any`, after the declaration of `any`. -/
private def anyAtParamProgram : Program :=
  { decls := .func anyFunction .empty :: (lemmaProgram "L" ["a"]
      (allOf (some (.ftvar "a"))
        (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.op Core.coreLoc ⟨"any", ()⟩ none)))).decls }

-- A polymorphic lemma whose stored annotations mention only its type parameter `a` is accepted.
/-- info: (ACCEPTED, [a]) -/
#guard_msgs in
#eval (programVerdict anyAtParamProgram, storedTypeVars anyAtParamProgram)

-- A polymorphic lemma that is well typed only when its type parameter `a` is `int` is rejected.
/-- info: REJECTED: Error in lemma L: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["a"]
  (allOf (some (.ftvar "a"))
    (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.const Core.coreLoc (.intConst 1)))))

-- An op annotation's type variables belong to the op: the lemma `L<a>` may use `idf` annotated
-- `a → a`, `c → c` or not at all at `bool`.
open Core.TestUtil (idfDecl idfTrueEq printIdfVerdicts) in
/--
info: ACCEPTED
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printIdfVerdicts fun ann =>
  { decls := idfDecl :: (lemmaProgram "L" ["a"] (idfTrueEq ann)).decls }

-- An annotation naming `$__rigid_a`, a type with the rigid prefix, is rejected.
/--
info: REJECTED: Error in lemma L: Type $__rigid_a is not an instance of a previously registered type!
-/
#guard_msgs in
#eval Core.TestUtil.firstLineOf (programVerdict (lemmaProgram "L" []
  (allOf (some (.tcons "$__rigid_a" [])) (.const Core.coreLoc (.boolConst true)))))

-- A free variable typed at the lemma's type parameter `a` is rejected.
/--
info: REJECTED: Error in lemma L: [(∀ (bvar:a) (%0 == (y : a)))] No free variables are allowed here!
Free Variables: [y]
-/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" ["a"]
  (allOf (some (.ftvar "a"))
    (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.fvar Core.coreLoc "y" (some (.ftvar "a"))))))

-- A lemma whose binder type nothing constrains is rejected.
/-- info: REJECTED: Lemma 'L' is typed at a generated type variable that is not declared -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" []
                      (allOf none (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))))

-- A lemma must have boolean type.
/-- info: REJECTED: Error in lemma L: Impossible to unify int with bool. -/
#guard_msgs in
#eval programVerdict (lemmaProgram "L" [] (.const Core.coreLoc (.intConst 1)))

-- A lemma reusing the name of an earlier lemma or axiom is rejected.
/--
info: REJECTED: Error in lemma L: a declaration of this name already exists.
REJECTED: Error in lemma L: a declaration of this name already exists.
-/
#guard_msgs in
#eval printEach [
  programVerdict { decls := [
    .lemma { name := "L", typeArgs := [], e := .const Core.coreLoc (.boolConst true) } .empty,
    .lemma { name := "L", typeArgs := [], e := .const Core.coreLoc (.boolConst true) } .empty] },
  programVerdict { decls := [
    .ax { name := "L", e := .const Core.coreLoc (.boolConst true) } .empty,
    .lemma { name := "L", typeArgs := [], e := .const Core.coreLoc (.boolConst true) } .empty] }]

-- Two axioms with one name, the second ill-typed: the type error is reported, not the
-- duplicate name.
/-- info: REJECTED: Error in axiom A: Impossible to unify int with bool. -/
#guard_msgs in
#eval programVerdict { decls := [
  .ax { name := "A", e := .const Core.coreLoc (.boolConst true) } .empty,
  .ax { name := "A", e := .const Core.coreLoc (.intConst 1) } .empty] }

end LemmaTypeCheckTests

/-! ## Distinct declaration type checking -/

namespace DistinctTypeCheckTests

open Lambda
open Core.TestUtil (allOf anyFunction generatedBinderOccurrence printEach programVerdict verdictOf)

/-- A program containing one distinct declaration. -/
private def distinctProgram (name : String) (es : List Expression.Expr) : Program :=
  { decls := [.distinct ⟨name, ()⟩ es .empty] }

/-- The direct distinct checker's verdict. -/
private def directVerdict (name : String) (es : List Expression.Expr) : Std.Format :=
  verdictOf (Core.Distinct.typeCheck initTyContext Lambda.TEnv.default ⟨name, ()⟩ es)

/-- A program declaring `any` and the distinct group `g` of `es`. -/
private def generatorProgram (es : List Expression.Expr) : Program :=
  { decls := [.func anyFunction .empty, .distinct ⟨"g", ()⟩ es .empty] }

/-- The returned type-variable generator counter, or zero when checking fails. -/
private def resultTyGen (program : Program) : Nat :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default program with
  | .ok (_, env) => env.genEnv.genState.tyGen
  | .error _ => 0

/-- An environment binding `y` at the open monotype `a`. -/
private def openScopeEnv : Expression.TyEnv :=
  Lambda.TEnv.default.updateContext
    { types := Strata.Util.HMaps.ofScopes
        [[(⟨"y", ()⟩, LTy.forAll [] (.ftvar "a"))]] }

/-- Type variables in the first expression stored by the distinct declaration. -/
private def firstStoredTypeVars : List String :=
  let program := distinctProgram "g"
    [.fvar Core.coreLoc ⟨"y", ()⟩ none,
     .const Core.coreLoc (.intConst 1)]
  match Core.Program.typeCheck initTyContext openScopeEnv program with
  | .ok ({ decls := [.distinct _ (e :: _) _] }, _) => (annotTyVars e).eraseDups
  | _ => ["rejected"]

-- A distinct group whose free variable has the generated binder's name is rejected.
/--
info: REJECTED: [(∀ (bvar:int) ($__var0 == #1))] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval programVerdict (distinctProgram "g"
  [allOf (some .int) (.eq Core.coreLoc generatedBinderOccurrence
                      (.const Core.coreLoc (.intConst 1))),
   .const Core.coreLoc (.boolConst true)])

-- A distinct group containing a binder whose type nothing constrains is rejected.
/-- info: REJECTED: Distinct 'g' is typed at a generated type variable that is not declared -/
#guard_msgs in
#eval programVerdict (distinctProgram "g"
  [allOf none (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0)),
   .const Core.coreLoc (.boolConst true)])

-- The type-variable generator state is threaded through the expressions: a group of three
-- `any` uses ends with a larger counter than a group of two.
/-- info: true -/
#guard_msgs in
#eval resultTyGen (generatorProgram
    [.eq Core.coreLoc (.op Core.coreLoc ⟨"any", ()⟩ none) (.const Core.coreLoc (.intConst 1)),
     .eq Core.coreLoc (.op Core.coreLoc ⟨"any", ()⟩ none) (.const Core.coreLoc (.boolConst true))])
  < resultTyGen (generatorProgram
    [.eq Core.coreLoc (.op Core.coreLoc ⟨"any", ()⟩ none) (.const Core.coreLoc (.intConst 1)),
     .eq Core.coreLoc (.op Core.coreLoc ⟨"any", ()⟩ none) (.const Core.coreLoc (.boolConst true)),
     .eq Core.coreLoc (.op Core.coreLoc ⟨"any", ()⟩ none) (.const Core.coreLoc (.intConst 2))])

-- A solution learned from a later expression is applied to every expression before storage.
/-- info: [] -/
#guard_msgs in
#eval firstStoredTypeVars

-- Accepted: a reference to the quantifier's own binder, and an omitted binder type the body fixes.
/--
info: ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach [
  programVerdict (distinctProgram "g"
    [allOf (some .int) (.eq Core.coreLoc (.bvar Core.coreLoc 0)
                        (.const Core.coreLoc (.intConst 1))),
     .const Core.coreLoc (.boolConst true)]),
  programVerdict (distinctProgram "g"
    [allOf none (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.const Core.coreLoc (.intConst 1))),
      .const Core.coreLoc (.boolConst true)])]

/-- The program checker's and the direct distinct checker's verdicts on one group. -/
private def bothVerdicts (name : String) (es : List Expression.Expr) : List Std.Format :=
  [programVerdict (distinctProgram name es), directVerdict name es]

-- Expressions in one group must all have the same type.
/--
info: REJECTED: Distinct 'g': #1 has type int but #true has type bool
REJECTED: Distinct 'g': #1 has type int but #true has type bool
-/
#guard_msgs in
#eval printEach (bothVerdicts "g"
                 [.const Core.coreLoc (.intConst 1), .const Core.coreLoc (.boolConst true)])

-- A group must contain at least two expressions; two expressions of the same type are accepted.
/--
info: REJECTED: Distinct 'g' must contain at least two expressions
REJECTED: Distinct 'g' must contain at least two expressions
REJECTED: Distinct 'g' must contain at least two expressions
REJECTED: Distinct 'g' must contain at least two expressions
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach (bothVerdicts "g" [] ++ bothVerdicts "g" [.const Core.coreLoc (.intConst 1)] ++
  bothVerdicts "g" [.const Core.coreLoc (.intConst 1), .const Core.coreLoc (.intConst 2)])

-- A reserved generated name is accepted as a distinct name.
/--
info: ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach (bothVerdicts "$__ty0"
                 [.const Core.coreLoc (.intConst 1), .const Core.coreLoc (.intConst 2)])

-- An annotation naming `$__rigid_a`, a type with the rigid prefix, is rejected; an ordinary
-- annotation is accepted.
/--
info: REJECTED: Type $__rigid_a is not an instance of a previously registered type!
REJECTED: Type $__rigid_a is not an instance of a previously registered type!
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printEach
  ((bothVerdicts "g"
    [allOf (some (.tcons "$__rigid_a" [])) (.const Core.coreLoc (.boolConst true)),
     .const Core.coreLoc (.boolConst false)] ++
   bothVerdicts "g" [allOf (some .int) (.const Core.coreLoc (.boolConst true)), .const Core.coreLoc
                     (.boolConst false)])
    |>.map Core.TestUtil.firstLineOf)

-- A binder typed at type variable `b` is rejected: `b` is not in scope.
/--
info: REJECTED: Error in distinct g: type variable `b` is not in scope
REJECTED: Error in distinct g: type variable `b` is not in scope
-/
#guard_msgs in
#eval printEach
  (bothVerdicts "g"
    [allOf (some (.ftvar "b")) (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0)),
      .const Core.coreLoc (.boolConst false)])

-- A free variable annotated at the rigid-parameter type variable `$__rigid_a` is rejected: a
-- distinct declaration has no type parameters, so no rigid type variable is in scope.
/--
info: REJECTED: Error in distinct g: type variable `$__rigid_a` is not in scope
REJECTED: Error in distinct g: type variable `$__rigid_a` is not in scope
-/
#guard_msgs in
#eval printEach
  (bothVerdicts "g"
    [.fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "$__rigid_a")), .const Core.coreLoc
      (.boolConst false)])

-- A free variable annotated at the generated type variable `$__ty0` is rejected: no generated
-- type variable is in scope.
/--
info: REJECTED: Error in distinct g: type variable `$__ty0` is not in scope
REJECTED: Error in distinct g: type variable `$__ty0` is not in scope
-/
#guard_msgs in
#eval printEach
  (bothVerdicts "g"
    [.fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "$__ty0")), .const Core.coreLoc (.boolConst false)])

-- Applying `1` to `true` is rejected; the unsolved result type prints as `_`.
/-- info: REJECTED: Impossible to unify int with (arrow bool _). -/
#guard_msgs in
#eval programVerdict (distinctProgram "g"
  [.app Core.coreLoc (.const Core.coreLoc (.intConst 1)) (.const Core.coreLoc (.boolConst true)),
   .const Core.coreLoc (.boolConst false)])

/-- A program declaring a polymorphic list datatype. -/
private def listProgramSrc :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };
#end

/-- `Nil()` and `Cons(1, Nil())` as a distinct group. -/
private def nilConsGroup : List Expression.Expr :=
  let nil : Expression.Expr := .op Core.coreLoc ⟨"Nil", ()⟩ none
  let cons : Expression.Expr := .op Core.coreLoc ⟨"Cons", ()⟩ none
  [nil, .app Core.coreLoc (.app Core.coreLoc cons (.const Core.coreLoc (.intConst 1))) nil]

/-- The operators of an expression with their annotations, left to right. -/
private def opAnnotations : Expression.Expr → List String
  | .op _ c ty => [s!"{c.name} : {Std.format ty}"]
  | .app _ f a => opAnnotations f ++ opAnnotations a
  | _ => []

-- The type the group's expressions share reaches every output annotation: both `Nil` operators
-- are annotated `List int`.
/--
info: Nil : some (List int)
Cons : some (arrow int (arrow (List int) (List int))), Nil : some (List int)
-/
#guard_msgs in
#eval
  let listDecls := (Core.TestUtil.translateWithMetaData listProgramSrc).decls
  let prog : Core.Program :=
    { decls := listDecls ++ [.distinct ⟨"d", ()⟩ nilConsGroup .empty] }
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default prog with
  | .ok ({ decls := ds }, _) =>
    match ds.getLast? with
    | some (.distinct _ es _) =>
      printEach (es.map fun e => Std.format (", ".intercalate (opAnnotations e)))
    | _ => printEach []
  | .error _ => printEach []

end DistinctTypeCheckTests

section ClauseTypeVarTests
open Std (ToFormat Format format)
open Lambda Strata
open Core.TestUtil (programVerdict translate)

/-! ## A generated type variable must not reach a stored function expression

No body, measure, precondition or axiom may keep an unconstrained generated type variable. -/

/-! ### A callee whose type parameter no call site constrains

A call `loose()` with no type argument does not fix `loose`'s type parameter. -/

/-- A function with two preconditions that each call `loose()` is rejected. -/
private def looseSiblingClausesPgm :=
#strata
program Core;

function loose<a>() : Sequence a;
function g(x : int) : int requires (Sequence.length(loose()) == 0);
                          requires (Sequence.length(loose()) == 1); { int.safeDiv(x, 0) }
#end

/--
info: REJECTED: Function 'g': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval programVerdict (translate looseSiblingClausesPgm)

/-- A body calling `loose()` is rejected: the output type fixes the body's type but not the
    element type of `loose()`. -/
private def looseBodyPgm :=
#strata
program Core;

function loose<a>() : Sequence a;
function gb(x : int) : int { Sequence.length(loose()) }
#end

/--
info: REJECTED: Function 'gb': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval programVerdict (translate looseBodyPgm)

/-- A single precondition calling `loose()` is rejected. -/
private def looseOneClausePgm :=
#strata
program Core;

function loose<a>() : Sequence a;
function gs(x : int) : int requires (Sequence.length(loose()) == 0); { x }
#end

/--
info: REJECTED: Function 'gs': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval programVerdict (translate looseOneClausePgm)

/-! ### Accepted shapes -/

/-- The declaration of `loose` alone is accepted. -/
private def looseAlonePgm :=
#strata
program Core;

function loose<a>() : Sequence a;
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate looseAlonePgm)

/-- Preconditions calling `Sequence.empty` with explicit type arguments are accepted. -/
private def seqEmptyPgm :=
#strata
program Core;

function h(s : Sequence int) : bool
  requires (Sequence.length(Sequence.empty<int>()) == 0);
  requires (Sequence.length(Sequence.empty<bool>()) == 0);
  { Sequence.length(s) == 0 }
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate seqEmptyPgm)

/-- A precondition naming the function's own type parameter is accepted. -/
private def polyClausePgm :=
#strata
program Core;

function ident<a>(x : a) : a
  requires (forall y : a :: y == y);
  { x }
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate polyClausePgm)

/-! ### Explicit and missing element types for `Set.empty`

A precondition equating two empty sets needs an element-type annotation. -/

/-- A function `k` whose precondition equates the empty set of element type `elemTy`
    (unannotated when `none`) with itself. -/
private def setEmptyPgm (elemTy : Option LMonoTy) : Program :=
  { decls :=
      [.func { name := "k", typeArgs := [], inputs := [], output := .bool,
               body := some (.const Core.coreLoc (.boolConst true)),
               preconditions :=
                 [{ expr := LExpr.eq Core.coreLoc (Core.setEmptyOp elemTy) (Core.setEmptyOp elemTy),
                    md := Core.coreLoc }] } .empty] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (setEmptyPgm (some LMonoTy.int))

/--
info: REJECTED: Function 'k': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval programVerdict (setEmptyPgm none)

end ClauseTypeVarTests

end Core

/-! ## Extra factory functions in `Core.typeCheck`

Extra functions are checked before the program, against the built-ins and earlier extra
functions. -/

namespace Strata.ExtraFactoryTypeCheckTests

open Lambda
open StrataDDM (Program)
open Core.TestUtil (coreVerdict translate)

/-- Whether a declaration is a function declaration named `n`. -/
def isFuncNamed (n : String) : Core.Decl → Bool
  | .func f _ => f.name.name == n
  | _ => false

/-- Move the functions named in `names` out of `p` into a factory of bodyless extra functions. -/
def split (p : Core.Program) (names : List String) : Core.Program × Factory Core.CoreLParams :=
  let fns := p.decls.filterMap fun d => match d with
    | .func f _ =>
      if names.contains f.name.name then some (LFuncDefined.toLFunc { f with body := none } none)
      else none
    | _ => none
  ({ decls := p.decls.filter fun d => !names.any (isFuncNamed · d) }, Factory.ofArray fns.toArray)

/-- The outcome of type checking `split p names`. -/
def check (p : Program) (names : List String) : Std.Format :=
  let (q, fns) := split (translate p) names
  coreVerdict q none fns

private def builtinTypedPgm : Program :=
#strata
program Core;
function mkI(x : int) : int;
axiom [refl]: mkI(3) == mkI(3);
#end

-- An extra function over built-in types may be called by the program.
/-- info: ACCEPTED -/
#guard_msgs in
#eval check builtinTypedPgm ["mkI"]

private def myTPgm : Program :=
#strata
program Core;
datatype MyT () { A(), B() };
function mkT(x : int) : MyT;
axiom [isA]: MyT..isA(mkT(3));
axiom [refl]: mkT(3) == mkT(3);
#end

-- A signature may not name a datatype the program declares.
/-- info: REJECTED: Function 'mkT': signature type MyT is not a registered type -/
#guard_msgs in
#eval check myTPgm ["mkT"]

/-- A polymorphic function whose body calls the extra function `g`, unannotated, on its argument. -/
private def reservedSignatureCaller : Core.Program := { decls := [
  .func { name := "f", typeArgs := ["a"], inputs := [("x", .ftvar "a")], output := .int,
          body := some (.app Core.coreLoc (.op Core.coreLoc "g" none) (.fvar Core.coreLoc "x" none))
              } .empty ] }

/-- An extra function `g` whose input type is the reserved constructor `$__rigid_a`. -/
private def reservedSignatureFns : Factory Core.CoreLParams :=
  Factory.ofArray #[{ name := "g", inputs := [("y", .tcons "$__rigid_a" [])], output := .int }]

-- An extra function whose signature names the unregistered type `$__rigid_a` is rejected.
/-- info: REJECTED: Function 'g': signature type $__rigid_a is not a registered type -/
#guard_msgs in
#eval coreVerdict reservedSignatureCaller none reservedSignatureFns

private def badPreconditionPgm : Program :=
#strata
program Core;
function g(x : int) : int requires (x); { 0 }
axiom [refl]: g(3) == g(3);
#end

-- The conditions of an extra function are checked.
/-- info: REJECTED: Impossible to unify int with bool. -/
#guard_msgs in
#eval check badPreconditionPgm ["g"]

private def synonymPgm : Program :=
#strata
program Core;
datatype MyT () { A(), B() };
type Syn := MyT;
function mkS(x : int) : Syn;
axiom [isA]: MyT..isA(mkS(3));
#end

-- A signature may not name a synonym the program declares.
/-- info: REJECTED: Function 'mkS': signature type Syn is not a registered type -/
#guard_msgs in
#eval check synonymPgm ["mkS"]

private def intSynonymPgm : Program :=
#strata
program Core;
type MyInt := int;
function f(x : MyInt) : MyInt;
axiom [fx]: f(3) == f(3);
#end

-- A signature may not name a synonym of a built-in type either.
/-- info: REJECTED: Function 'f': signature type MyInt is not a registered type -/
#guard_msgs in
#eval check intSynonymPgm ["f"]

private def paramCollisionPgm : Program :=
#strata
program Core;
function f(y : int) : int;
function mkI(f : int) : int;
axiom [refl]: mkI(3) == mkI(3);
#end

-- A parameter of an extra function may not share its name with an earlier extra function.
/--
info: REJECTED: Function 'mkI': parameter 'f' collides with a function or constant of the same name
-/
#guard_msgs in
#eval check paramCollisionPgm ["f", "mkI"]

private def programParamPgm : Program :=
#strata
program Core;
function mkI(f : int) : int;
function f(y : int) : int { y }
axiom [refl]: mkI(3) == f(3);
#end

-- A parameter of an extra function may share its name with a program function.
/-- info: ACCEPTED -/
#guard_msgs in
#eval check programParamPgm ["mkI"]

-- An extra function may not share its name with a built-in function.
/--
info: REJECTED: A function of name Int.Add already exists! Redefinitions are not allowed.
Existing Function: func Int.Add :  ((x : int) (y : int)) → int;
New Function:func Int.Add :  ((x : int)) → int;
-/
#guard_msgs in
#eval coreVerdict { decls := [] } none
  (Factory.ofArray #[{ name := "Int.Add", inputs := [("x", .int)], output := .int }])

private def programGPgm : Core.Program := { decls := [
  .func { name := "g", inputs := [("x", .int)], output := .int, body := none } .empty ] }

-- A program function may not share its name with an extra function.
/-- info: REJECTED: Error in function g: a function of this name already exists. -/
#guard_msgs in
#eval coreVerdict programGPgm none
  (Factory.ofArray #[{ name := "g", inputs := [("y", .int)], output := .int }])

/-- Extra functions `g` and `h`, where the body of `h` calls `g`; `g` comes first when
    `calleeFirst`. -/
private def callerFns (calleeFirst : Bool) : Lambda.Factory Core.CoreLParams :=
  let g : Lambda.LFunc Core.CoreLParams := { name := "g", inputs := [("x", .int)], output := .int }
  let h : Lambda.LFunc Core.CoreLParams :=
    { name := "h", inputs := [("y", .int)], output := .int,
      body := some (.app Core.coreLoc (.op Core.coreLoc "g" none) (.fvar Core.coreLoc "y" none)) }
  Lambda.Factory.ofArray (if calleeFirst then #[g, h] else #[h, g])

-- The body of an extra function may call an earlier extra function.
/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict { decls := [] } (some .default) (callerFns true)

-- The body of an extra function may not call a later extra function.
/-- info: REJECTED: Function names: #[] Cannot infer the type of this operation: `g` -/
#guard_msgs in
#eval coreVerdict { decls := [] } (some .default) (callerFns false)

/-- An extra identity function whose type parameter `$__ty0` has a reserved prefix. -/
private def reservedTyParamFns : Lambda.Factory Core.CoreLParams :=
  let ident : Lambda.LFunc Core.CoreLParams :=
    { name := "ident", typeArgs := ["$__ty0"], inputs := [("x", .ftvar "$__ty0")],
      output := .ftvar "$__ty0" }
  Lambda.Factory.ofArray #[ident]

/-- The function named `n` that check-then-add of `fns` registers after the built-ins. -/
private def registered (fns : Lambda.Factory Core.CoreLParams) (n : String) : Std.Format :=
  match Core.Factory.checkThenAdd { Core.initTyContext with functions := Core.Factory }
      Lambda.TEnv.default fns.toArray with
  | .ok C => match C.functions[n]? with
    | some f => Std.format f
    | none => "not registered"
  | .error e => s!"REJECTED: {e.message}"

-- An extra function with a reserved type parameter is accepted and registered with the
-- parameter renamed.
/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict { decls := [] } none reservedTyParamFns

/-- info: func ident : ∀[a]. ((x : a)) → a; -/
#guard_msgs in
#eval registered reservedTyParamFns "ident"

/-- An extra function `g<p> (x : int) : int`, whose type parameter `p` occurs
    in neither an input type nor the output type. -/
private def phantomTyParamFns : Lambda.Factory Core.CoreLParams :=
  Lambda.Factory.ofArray
    #[{ name := "g", typeArgs := ["p"], inputs := [("x", .int)],
        output := .int }]

-- An extra function with a type parameter its signature does not mention is
-- rejected.
/--
info: REJECTED: Function 'g': type parameters [p] occur in neither an input
type nor the output type, so a call could not determine them
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict { decls := [] } none phantomTyParamFns

end Strata.ExtraFactoryTypeCheckTests

/-! ## The factory argument of `Core.typeCheck` -/

namespace Core.FactoryArgTests

open Strata.ExtraFactoryTypeCheckTests (myTPgm reservedSignatureFns phantomTyParamFns)
open Core.TestUtil (coreVerdict translate)

-- A program is accepted with the built-in factory, as `none` or as `some Core.Factory`.
/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict (translate myTPgm) none

/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict (translate myTPgm) (some Core.Factory)

-- A supplied factory whose signature names the unregistered type `$__rigid_a` is rejected.
/-- info: REJECTED: Function 'g': signature type $__rigid_a is not a registered type -/
#guard_msgs in
#eval coreVerdict (translate myTPgm) (some reservedSignatureFns)

-- A supplied factory with a type parameter its signature does not mention is
-- rejected.
/--
info: REJECTED: Function 'g': type parameters [p] occur in neither an input
type nor the output type, so a call could not determine them
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict { decls := [] } (some phantomTyParamFns)

end Core.FactoryArgTests

/-! ## Function-name collision tests

A function or local variable may not reuse the name of a visible function. -/

namespace Strata.BuiltinNameCollisionTest

open Std (ToFormat Format format)
open StrataDDM (Program)
open Core.TestUtil (coreVerdict translate)

-- Rejected: a function whose name is a builtin's name.

def selectCollisionPgm : Program :=
#strata
program Core;

function select (b : bool) : bool { b }
#end

/--
info: REJECTED: Error in function select: a function of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate selectCollisionPgm)

def updateCollisionPgm : Program :=
#strata
program Core;

function update (b : bool) : bool { b }
#end

/--
info: REJECTED: Error in function update: a function of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate updateCollisionPgm)

-- A function declaration may not reuse the builtin name `mapConst`.
private def mapConstCollisionPgm : Core.Program := { decls := [
  .func { name := "mapConst", inputs := [], output := .tcons "bool" [] } .empty
]}

/--
info: REJECTED: Error in function mapConst: a function of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict mapConstCollisionPgm

-- Rejected: a recursive function block whose name is a builtin's name.

def recBlockCollisionPgm : Program :=
#strata
program Core;

rec function select (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else select(int.sub(n, 1))
};
#end

/--
info: REJECTED: Error in function select: a function of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate recBlockCollisionPgm)

-- Accepted: a name that merely contains a builtin's name as a substring.

def substringNamePgm : Program :=
#strata
program Core;

function selectFoo (b : bool) : bool { b }
function fooSelect (b : bool) : bool { b }
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate substringNamePgm)

-- Accepted: two functions with fresh, distinct names.

def twoFreshFunctionsPgm : Program :=
#strata
program Core;

function idBool (b : bool) : bool { b }
function notBool (b : bool) : bool { if b then false else true }
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate twoFreshFunctionsPgm)

-- Accepted: a function declared before a datatype whose generated functions have other names.

def functionBeforeDatatypePgm : Program :=
#strata
program Core;

function idBool (b : bool) : bool { b }

datatype Color { Red(), Green() };

function isRedAgain (c : Color) : bool { Color..isRed(c) }
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate functionBeforeDatatypePgm)

-- Accepted: a recursive function block with a fresh name.

def recBlockFreshNamePgm : Program :=
#strata
program Core;

rec function countdown (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate recBlockFreshNamePgm)

-- Rejected: a recursive block member with a parameter named after another member of the block.

def recBlockParamCollisionPgm : Program :=
#strata
program Core;

rec function f (g : int) : int
  decreases g
{
  if int.le(g, 0) then 0 else f(int.sub(g, 1))
}
function g (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else f(int.sub(n, 1))
};
#end

/--
info: REJECTED: Function 'f': parameter 'g' collides with a function or constant of the same name
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate recBlockParamCollisionPgm)

-- A body-local `function` declares a local variable, which may not reuse a builtin's name.

def nestedSelectCollisionPgm : Program :=
#strata
program Core;

procedure P()
{
  function select (b : bool) : bool { b }
};
#end

/--
info: REJECTED: Procedure 'P': Local variable 'select' collides with a function or constant of the same name
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedSelectCollisionPgm)

-- A local variable may not reuse a datatype constructor's name.
def nestedConstructorCollisionPgm : Program :=
#strata
program Core;

datatype Box { MkBox(boxVal: int) };

procedure P()
{
  function MkBox (x : int) : int { x }
};
#end

/--
info: REJECTED: Procedure 'P': Local variable 'MkBox' collides with a function or constant of the same name
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedConstructorCollisionPgm)

-- A local variable may not reuse the name of a function declared earlier in the program.
def nestedEarlierFunctionCollisionPgm : Program :=
#strata
program Core;

function dup (x : int) : int { x }

procedure P()
{
  function dup (y : int) : int { y }
};
#end

/--
info: REJECTED: Procedure 'P': Local variable 'dup' collides with a function or constant of the same name
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedEarlierFunctionCollisionPgm)

-- A local variable may share its name with a function declared later in the program.
def nestedLaterFunctionCollisionPgm : Program :=
#strata
program Core;

procedure P()
{
  function late (y : int) : int { y }
};

function late (x : int) : int { x }
#end

/--
info: ACCEPTED
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedLaterFunctionCollisionPgm)

-- Accepted: local functions with fresh names, including one reading an enclosing variable.

def nestedFreshNamePgm : Program :=
#strata
program Core;

procedure P()
{
  function twice (x : int) : int { int.add(x, x) }
  var z : int := twice(2);
};
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedFreshNamePgm)

def nestedReadsEnclosingVarPgm : Program :=
#strata
program Core;

procedure P()
{
  var x : int := 1;
  function addX (y : int) : int { int.add(y, x) }
  var z : int := addX(5);
};
#end

/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate nestedReadsEnclosingVarPgm)

end Strata.BuiltinNameCollisionTest

end
