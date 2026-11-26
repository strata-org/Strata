/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

/-! ## Tests for TypeDecl -/

namespace Core
open Std (ToFormat Format format)
open Lambda.LTy.Syntax
open Lambda Imperative

/-- info: ∀[a, b, c]. (Foo a b c) -/
#guard_msgs in
#eval format $ TypeConstructor.toType { name := "Foo", params := ["a", "b", "c"] }

-- A synonym whose body omits a declared type argument is rejected.
private def phantomArgSynonymPgm : Program :=
  { decls := [
      .type (.syn { name := "Foo", typeArgs := ["a"], type := .int }) .empty
  ]}

/--
info: error: Type synonym 'Foo': type argument 'a' is not used in the definition
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default phantomArgSynonymPgm)

-- A synonym that uses every declared type argument is accepted.
private def usedArgSynonymPgm : Program :=
  { decls := [
      .type (.syn { name := "Bar", typeArgs := ["a"],
                    type := .tcons "Map" [.ftvar "a", .ftvar "a"] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type Bar (a : Type) := Map a a;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default usedArgSynonymPgm)

-- A constructor argument with an undeclared type variable is rejected.
private def unscopedDatatypeArgPgm : Program :=
  { decls := [
      .type (.data [
        { name := "Bad", typeArgs := [],
          constrs := [{ name := ⟨"C", ()⟩, args := [(⟨"x", ()⟩, .ftvar "a")] }],
          constrs_ne := by decide }
      ]) .empty
  ]}

/--
info: error: Datatype 'Bad': constructor 'C' uses type variable 'a' not in its type arguments
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default unscopedDatatypeArgPgm)

-- A constructor argument with a declared type variable is accepted.
private def scopedDatatypeArgPgm : Program :=
  { decls := [
      .type (.data [
        { name := "Box", typeArgs := ["a"],
          constrs := [{ name := ⟨"MkBox", ()⟩, args := [(⟨"val", ()⟩, .ftvar "a")] }],
          constrs_ne := by decide }
      ]) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

datatype Box (a : Type) {
  MkBox(val : a)
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default scopedDatatypeArgPgm)

-- A recursive datatype whose constructor argument is the datatype itself is accepted.
private def recursiveDatatypeArgPgm : Program :=
  { decls := [
      .type (.data [
        { name := "List", typeArgs := ["a"],
          constrs := [
            { name := ⟨"Nil", ()⟩, args := [] },
            { name := ⟨"Cons", ()⟩,
              args := [(⟨"hd", ()⟩, .ftvar "a"), (⟨"tl", ()⟩, .tcons "List" [.ftvar "a"])] }],
          constrs_ne := by decide }
      ]) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(hd : a, tl : List a)
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default recursiveDatatypeArgPgm)

-- A type name with the rigid-parameter prefix is accepted.
private def rigidPrefixTypeNamePgm : Program :=
  { decls := [
      .type (.con { name := "$__rigid_a", params := [] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type $__rigid_a;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidPrefixTypeNamePgm)

-- An ordinary type name is accepted.
private def ordinaryTypeNamePgm : Program :=
  { decls := [
      .type (.con { name := "MyType", params := [] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type MyType;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default ordinaryTypeNamePgm)

-- A type name with the `$__liftfncl` prefix is accepted.
private def transformPrefixTypeNamePgm : Program :=
  { decls := [
      .type (.con { name := "$__liftfncl_foo", params := [] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type $__liftfncl_foo;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default transformPrefixTypeNamePgm)

-- A type name with the eliminator-result prefix is accepted.
private def elimTyPrefixTypeNamePgm : Program :=
  { decls := [
      .type (.con { name := "$__elimty0", params := [] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type $__elimty0;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default elimTyPrefixTypeNamePgm)

-- Names resembling the eliminator-result prefix are accepted.
private def nearMissElimTyNamesPgm : Program :=
  { decls := [
      .type (.con { name := "$__elimt", params := [] }) .empty,
      .type (.con { name := "elimty0", params := [] }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type $__elimt;
type elimty0;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default nearMissElimTyNamesPgm)

/-! ### Type names with reserved prefixes in declarations

A declaration may name a type with a reserved prefix; the type must be registered like any
other. -/

section ReservedTypeNameTests

open Std (ToFormat Format format)
open Core.TestUtil (rigidA firstLineOf functionVerdict procedureVerdict programVerdict)
open Lambda Imperative

/-- The program context with the rigid constructor for `a` registered. -/
private def Crigid : Expression.TyContext :=
  addSkolemTypes initTyContext [("a", Core.skolemName "a")]

/-- A function-checking context with no ambient factory entries. -/
private def Cfunc : Expression.TyContext :=
  { LContext.default with knownTypes := Core.KnownTypes }

/-- `Cfunc` with the rigid constructor for `a` registered. -/
private def CrigidFunc : Expression.TyContext :=
  addSkolemTypes Cfunc [("a", Core.skolemName "a")]

/-! #### A procedure header -/

/-- A procedure whose input names a reserved rigid constructor. -/
private def procRigidInput : Procedure :=
  { header := { name := ⟨"q", ()⟩, typeArgs := ["a"], inputs := [(⟨"x", ()⟩, rigidA)],
                outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

/-- A procedure whose output names a reserved rigid constructor. -/
private def procRigidOutput : Procedure :=
  { header := { name := ⟨"r", ()⟩, typeArgs := ["a"], inputs := [],
                outputs := [(⟨"y", ()⟩, rigidA)] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

/-- info: REJECTED: Procedure 'q': signature type $__rigid_a is not a registered type -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procRigidInput initTyContext

/-- info: REJECTED: Procedure 'r': signature type $__rigid_a is not a registered type -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procRigidOutput initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procRigidInput Crigid

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procRigidOutput Crigid

/-- A procedure whose input and output use its declared type parameter. -/
private def procPolyOk : Procedure :=
  { header := { name := ⟨"s", ()⟩, typeArgs := ["a"], inputs := [(⟨"x", ()⟩, .ftvar "a")],
                outputs := [(⟨"y", ()⟩, .ftvar "a")] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procPolyOk initTyContext

/-! #### A factory function signature

A reserved rigid constructor is accepted when the context registers it. -/

/-- A factory function whose input and output use a reserved rigid constructor. -/
private def rigidFactoryFunction : Function :=
  { name := ⟨"rigidFactory", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, rigidA)], output := rigidA, body := none }

/-- A factory function with an ordinary Boolean signature. -/
private def ordinaryFactoryFunction : Function :=
  { name := ⟨"ordinaryFactory", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, .bool)], output := .bool, body := none }

/-- info: REJECTED: Function 'rigidFactory': signature type $__rigid_a is not a registered type -/
#guard_msgs in
#eval firstLineOf <| functionVerdict rigidFactoryFunction Cfunc

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| functionVerdict rigidFactoryFunction CrigidFunc

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| functionVerdict ordinaryFactoryFunction Cfunc

/-! #### A type synonym -/

/-- A synonym whose body is a reserved rigid constructor. -/
private def synRigidBody : Program :=
  { decls := [Decl.type (.syn { name := "MyT", typeArgs := [], type := rigidA }) .empty] }

/-- A synonym whose body nests a reserved rigid constructor. -/
private def synRigidNested : Program :=
  { decls := [Decl.type
      (.syn { name := "MyU", typeArgs := ["a"], type := .tcons "Map" [.ftvar "a", rigidA] })
      .empty] }

/-- A synonym whose own name is reserved. -/
private def synReservedName : Program :=
  { decls := [Decl.type
      (.syn { name := Core.skolemName "a", typeArgs := [], type := LMonoTy.int }) .empty] }

/-- A synonym whose type-parameter name is reserved. -/
private def synReservedTypeArg : Program :=
  { decls := [Decl.type
      (.syn { name := "MyW", typeArgs := [Core.skolemName "a"],
              type := .ftvar (Core.skolemName "a") })
      .empty] }

/-- A nullary synonym with an ordinary name and body. -/
private def synGood : Program :=
  { decls := [Decl.type (.syn { name := "Good", typeArgs := [], type := LMonoTy.int }) .empty] }

/-- A polymorphic synonym with ordinary parameter names. -/
private def synGoodPoly : Program :=
  { decls := [Decl.type
      (.syn { name := "GoodMap", typeArgs := ["a", "b"],
              type := .tcons "Map" [.ftvar "a", .ftvar "b"] })
      .empty] }

/-- info: REJECTED: Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| programVerdict synRigidBody initTyContext

/-- info: REJECTED: Type (Map a $__rigid_a) is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| programVerdict synRigidNested initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synReservedName initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synReservedTypeArg initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synGood initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synGoodPoly initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synRigidBody Crigid

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synRigidNested Crigid

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict synGood Crigid

/-! #### An opaque type declaration

Opaque type parameters may use reserved names, at program or procedure-body scope. -/

/-- A program-level opaque type with a reserved parameter name. -/
private def conReservedParam : Program :=
  { decls := [Decl.type (.con { name := "MyV", params := [Core.skolemName "a"] }) .empty] }

/-- A program-level opaque type with an ordinary parameter name. -/
private def conGoodParam : Program :=
  { decls := [Decl.type (.con { name := "MyV", params := ["a"] }) .empty] }

/-- A body-local opaque type with a reserved parameter name. -/
private def procConReservedParam : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured
      [@Imperative.Stmt.typeDecl Expression Command
        { name := "MyV", params := [Core.skolemName "a"] } .empty] false }

/-- A body-local opaque type with an ordinary parameter name. -/
private def procConGoodParam : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured
      [@Imperative.Stmt.typeDecl Expression Command { name := "MyV", params := ["a"] } .empty] false
          }

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict conReservedParam initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict conGoodParam initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procConReservedParam initTyContext

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict procConGoodParam initTyContext

end ReservedTypeNameTests

/-! ### A type synonym name may be introduced only once -/

-- Two synonyms of the same name and arity are rejected.
private def duplicateSynonymPgm : Program :=
  { decls := [
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty,
      .type (.syn { name := "T", typeArgs := [], type := .bool }) .empty
  ]}

/--
info: error: Error in type T: a declaration of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default duplicateSynonymPgm)

-- Two synonyms of the same name at different arities are rejected.
private def duplicateSynonymArityPgm : Program :=
  { decls := [
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty,
      .type (.syn { name := "T", typeArgs := ["a"],
                    type := .tcons "Map" [.ftvar "a", .bool] }) .empty
  ]}

/--
info: error: Error in type T: a declaration of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default duplicateSynonymArityPgm)

-- An opaque type and a later synonym of the same name are rejected.
private def opaqueThenSynonymPgm : Program :=
  { decls := [
      .type (.con { name := "T", params := [] }) .empty,
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty
  ]}

/--
info: error: Error in type T: a declaration of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default opaqueThenSynonymPgm)

-- Two synonyms with different names are accepted.
private def twoSynonymsPgm : Program :=
  { decls := [
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty,
      .type (.syn { name := "U", typeArgs := [], type := .bool }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type T := int;

type U := bool;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default twoSynonymsPgm)

-- A synonym may refer to an earlier synonym; it is stored with its body resolved.
private def chainedSynonymPgm : Program :=
  { decls := [
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty,
      .type (.syn { name := "U", typeArgs := [], type := .tcons "T" [] }) .empty,
      .func { name := "useU", inputs := [(⟨"x", ()⟩, .tcons "U" [])],
              output := .int } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type T := int;

type U := int;

function useU (x : int) : int;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default chainedSynonymPgm)

-- A procedure parameter written with a chained synonym is stored at the resolved type.
private def chainedSynonymProcPgm : Program :=
  { decls := [
      .type (.syn { name := "A", typeArgs := [], type := .int }) .empty,
      .type (.syn { name := "B", typeArgs := [], type := .tcons "A" [] }) .empty,
      .proc { header := { name := "p", typeArgs := [], inputs := [("x", .tcons "B" [])],
                          outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type A := int;

type B := int;

procedure p (x : int)
{
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default chainedSynonymProcPgm)

-- A parametric synonym over an earlier one is stored with its body resolved.
private def parametricChainPgm : Program :=
  { decls := [
      .type (.syn { name := "K", typeArgs := ["a"],
                    type := .tcons "Map" [.ftvar "a", .int] }) .empty,
      .type (.syn { name := "T", typeArgs := ["a"], type := .tcons "K" [.ftvar "a"] }) .empty,
      .func { name := "useT", inputs := [(⟨"x", ()⟩, .tcons "T" [.bool])],
              output := .int } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type K (a : Type) := Map a int;

type T (a : Type) := Map a int;

function useT (x : Map bool int) : int;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default parametricChainPgm)

-- A synonym and an opaque type with different names are accepted.
private def synonymAndOpaquePgm : Program :=
  { decls := [
      .type (.con { name := "Handle", params := [] }) .empty,
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type Handle;

type T := int;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default synonymAndOpaquePgm)

-- Differently named synonyms are accepted regardless of arity.
private def parameterizedSynonymPgm : Program :=
  { decls := [
      .type (.syn { name := "MyMap", typeArgs := ["a"],
                    type := .tcons "Map" [.ftvar "a", .bool] }) .empty,
      .type (.syn { name := "T", typeArgs := [], type := .int }) .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type MyMap (a : Type) := Map a bool;

type T := int;
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default parameterizedSynonymPgm)

/-! ### Body-local type names -/

-- A nullary body-local type with the rigid-parameter prefix is accepted.
private def bodyLocalRigidPrefixTypePgm : Program := { decls := [
  .proc { header := { name := "p", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "$__rigid_a", params := [] } .empty
          ] false } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure p ()
{
  type $__rigid_a;
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalRigidPrefixTypePgm)

-- A parameterized body-local type with the rigid-parameter prefix is accepted.
private def bodyLocalRigidPrefixTypeArityPgm : Program := { decls := [
  .proc { header := { name := "p", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "$__rigid_a", params := ["T"] } .empty
          ] false } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure p ()
{
  type $__rigid_a (T : Type);
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalRigidPrefixTypeArityPgm)

-- A body-local type with the generated-variable prefix is accepted.
private def bodyLocalGenPrefixTypePgm : Program := { decls := [
  .proc { header := { name := "p", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "$__ty0", params := [] } .empty
          ] false } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure p ()
{
  type $__ty0;
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalGenPrefixTypePgm)

-- An ordinary body-local opaque type and a following variable of that type are accepted.
private def bodyLocalOpaqueTypePgm : Program := { decls := [
  .proc { header := { name := "p", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "T", params := [] } .empty,
            Statement.init "x" (.forAll [] (.tcons "T" [])) .nondet .empty
          ] false } .empty
]}

/-- info: ACCEPTED -/
#guard_msgs in
#eval Core.TestUtil.coreVerdict bodyLocalOpaqueTypePgm

-- Names that only resemble a reserved prefix are accepted.
private def bodyLocalNearMissTypePgm : Program := { decls := [
  .proc { header := { name := "p", typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            .typeDecl { name := "$__rigi", params := [] } .empty,
            .typeDecl { name := "rigid_a", params := [] } .empty
          ] false } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure p ()
{
  type $__rigi;
  type rigid_a;
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyLocalNearMissTypePgm)

end Core

namespace Strata.AliasKnownTypeCollisionTests

open Std (ToFormat Format format)
open StrataDDM (Program)
open Core.TestUtil (coreVerdict translate)

/-! ## Duplicate type declarations -/

-- A synonym and a later opaque type cannot share a name.
/--
error: 'foo' already defined
-/
#guard_msgs in
private def synonymThenOpaquePgm : Program :=
#strata
program Core;

type foo := int;
type foo;
#end

-- An opaque type and a later synonym cannot share a name.
/--
error: 'foo' already defined
-/
#guard_msgs in
private def opaqueThenSynonymPgm : Program :=
#strata
program Core;

type foo;
type foo := int;
#end

-- A synonym and a later datatype cannot share a name.
/--
error: Type 'foo' is already declared.
-/
#guard_msgs in
private def synonymThenDatatypePgm : Program :=
#strata
program Core;

type foo := int;
datatype foo { mkFoo(x : int) };
#end

-- A datatype and a later synonym cannot share a name.
/--
error: 'foo' already defined
-/
#guard_msgs in
private def datatypeThenSynonymPgm : Program :=
#strata
program Core;

datatype foo { mkFoo(x : int) };
type foo := int;
#end

/-! ## Distinct type names -/

private def twoDifferentNamesPgm : Program :=
#strata
program Core;

type foo := int;
type bar;
#end

-- A synonym and an opaque type with distinct names are accepted.
/--
info: ok: program Core;

type foo := int;
type bar;
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translate twoDifferentNamesPgm)

private def synonymAlonePgm : Program :=
#strata
program Core;

type foo := int;
#end

-- A lone synonym is accepted.
/--
info: ok: program Core;

type foo := int;
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translate synonymAlonePgm)

private def opaqueAlonePgm : Program :=
#strata
program Core;

type foo;
#end

-- A lone opaque type is accepted.
/--
info: ok: program Core;

type foo;
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translate opaqueAlonePgm)

private def synonymOverEarlierOpaquePgm : Program :=
#strata
program Core;

type ref;
type heap := Map ref int;
#end

-- A synonym referring to an earlier opaque type is accepted.
/--
info: ok: program Core;

type ref;
type heap := Map ref int;
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translate synonymOverEarlierOpaquePgm)

private def datatypeThenSynonymOverItPgm : Program :=
#strata
program Core;

datatype dfoo { mkDfoo(x : int) };
type dbar := dfoo;
#end

-- A synonym referring to an earlier datatype is accepted.
/--
info: ok: program Core;

datatype dfoo {
  mkDfoo(x : int)
};
type dbar := dfoo;
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translate datatypeThenSynonymOverItPgm)

/-! ## Opaque types declared inside procedure bodies -/

private def bodyLocalOpaqueUnrelatedPgm : Program :=
#strata
program Core;

type foo := int;
procedure p() {
  type bar;
};
#end

-- A body-local opaque type and a program-level synonym with distinct names are accepted.
/-- info: ACCEPTED -/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate bodyLocalOpaqueUnrelatedPgm)

end Strata.AliasKnownTypeCollisionTests

/-! ## Program and context collision checks -/

namespace Core.AliasKnownTypeCollisionTests

open Std (ToFormat Format format)
open Lambda Imperative
open Strata (Message)
open Core.TestUtil (aliasEnv firstLine)

/-- A nullary synonym named `foo`. -/
def fooSynonym : TypeSynonym := { typeArgs := [], name := "foo", type := .int }

def fooAlias : TypeAlias := { typeArgs := [], name := "foo", type := .int }

/-- A nullary opaque type named `foo`. -/
def fooTypeConstructor : TypeConstructor := { name := "foo", params := [] }

/-- A datatype named `foo`. -/
def fooDatatype : LDatatype Unit :=
  { name := "foo", typeArgs := [],
    constrs := [{ name := ⟨"mkFoo", ()⟩, args := [(⟨"x", ()⟩, .int)] }],
    constrs_ne := rfl }

/-! ### Whole-program verdicts -/

/-- A synonym followed by an opaque type with the same name. -/
def synonymThenOpaqueProgram : Program :=
  { decls := [ .type (.syn fooSynonym) ∅, .type (.con fooTypeConstructor) ∅ ] }

/-- A synonym followed by a datatype with the same name. -/
def synonymThenDatatypeProgram : Program :=
  { decls := [ .type (.syn fooSynonym) ∅, .type (.data [fooDatatype]) ∅ ] }

/-- A datatype followed by a synonym with the same name. -/
def datatypeThenSynonymProgram : Program :=
  { decls := [ .type (.data [fooDatatype]) ∅, .type (.syn fooSynonym) ∅ ] }

/-- The first line of the program checker's message for `p`, or `accepted`. -/
def programTypeCheckVerdict (p : Program) (C : Expression.TyContext := initTyContext)
    (Env : Expression.TyEnv := Lambda.TEnv.default) : String :=
  match Core.Program.typeCheck C Env p with
  | .ok _ => "accepted"
  | .error e => firstLine (toString (format e))

-- A synonym cannot share a name with an opaque type or a datatype.
/--
info: "Error in type foo: a declaration of this name already exists."
-/
#guard_msgs (whitespace := lax) in
#eval programTypeCheckVerdict synonymThenOpaqueProgram

/--
info: "Error in type foo: a declaration of this name already exists."
-/
#guard_msgs (whitespace := lax) in
#eval programTypeCheckVerdict synonymThenDatatypeProgram

/--
info: "Error in type foo: a declaration of this name already exists."
-/
#guard_msgs (whitespace := lax) in
#eval programTypeCheckVerdict datatypeThenSynonymProgram

/-- A program containing only an opaque type. -/
def opaqueAloneProgram : Program := { decls := [ .type (.con fooTypeConstructor) ∅ ] }

/-! ### Ambient aliases

The checker takes the ambient aliases as given and does not validate them against the name
registry or check that their bodies name registered types. -/

/-- An environment whose aliases bind `foo` to `int`. -/
def envWithFooAlias : Expression.TyEnv := aliasEnv [fooAlias]

/-- The initial context with `names` added to the declaration-name registry. -/
def contextWithOccupiedNames (names : List String) : Expression.TyContext :=
  { initTyContext with
      idents := names.foldl (fun idents name => idents.insert name ()) initTyContext.idents }

/-- A context whose declaration-name registry includes the ambient alias `foo`. -/
def contextWithFooAlias : Expression.TyContext := contextWithOccupiedNames ["foo"]

/-- The verdict on an empty program from a supplied ambient context and type environment. -/
def ambientVerdict (C : Expression.TyContext) (Env : Expression.TyEnv) : String :=
  programTypeCheckVerdict { decls := [] } C Env

/-- An ambient alias `old` whose body names the unregistered constructor `ghost`. -/
def oldGhostEnv : Expression.TyEnv :=
  aliasEnv [{ name := "old", typeArgs := [], type := .tcons "ghost" [] }]

/-- Two ambient aliases introducing the same name. -/
def duplicateAliasEnv : Expression.TyEnv :=
  aliasEnv [
    { name := "dup", typeArgs := [], type := .int },
    { name := "dup", typeArgs := [], type := .bool }]

/-- An ambient alias whose name is also a built-in known type. -/
def knownTypeAliasEnv : Expression.TyEnv :=
  aliasEnv [{ name := "int", typeArgs := [], type := .int }]

/-- An ambient alias whose body applies `Map` to one argument. -/
def wrongStoredArityEnv : Expression.TyEnv :=
  aliasEnv [{ name := "badMap", typeArgs := [], type := .tcons "Map" [.int] }]

-- Ambient aliases that clash with the name registry or name unregistered types are not
-- rejected: the checker does not validate them.
/-- info: ["accepted", "accepted", "accepted", "accepted"] -/
#guard_msgs (whitespace := lax) in
#eval [ambientVerdict (contextWithOccupiedNames ["old"]) oldGhostEnv,
  ambientVerdict (contextWithOccupiedNames ["int"]) knownTypeAliasEnv,
  ambientVerdict initTyContext envWithFooAlias,
  ambientVerdict (contextWithOccupiedNames ["badMap"]) wrongStoredArityEnv]

-- An alias registered in the context, two aliases of one name with different bodies, and the
-- default environment are accepted.
/-- info: ["accepted", "accepted", "accepted"] -/
#guard_msgs (whitespace := lax) in
#eval [ambientVerdict contextWithFooAlias envWithFooAlias,
  ambientVerdict (contextWithOccupiedNames ["dup"]) duplicateAliasEnv,
  ambientVerdict initTyContext Lambda.TEnv.default]

-- An ambient alias prevents later opaque types and datatypes from reusing its name.
/-- info: "Error in type foo: a declaration of this name already exists." -/
#guard_msgs (whitespace := lax) in
#eval programTypeCheckVerdict opaqueAloneProgram contextWithFooAlias envWithFooAlias

/-- info: "Error in type foo: a declaration of this name already exists." -/
#guard_msgs (whitespace := lax) in
#eval programTypeCheckVerdict { decls := [ .type (.data [fooDatatype]) ∅ ] } contextWithFooAlias
  envWithFooAlias

-- A program declaration cannot reuse a name in the ambient identifier registry.
/--
info: ["Error in type foo: a declaration of this name already exists.",
  "Error in function foo: a declaration of this name already exists."]
-/
#guard_msgs (whitespace := lax) in
#eval [programTypeCheckVerdict opaqueAloneProgram (contextWithOccupiedNames ["foo"]),
  programTypeCheckVerdict { decls := [ .func { name := "foo", inputs := [], output := .int } ∅ ] }
    (contextWithOccupiedNames ["foo"])]

/-! ### Direct opaque-type checks with an ambient alias -/

/-- A unary opaque type named `foo`. -/
def fooTypeConstructorOneParam : TypeConstructor := { name := "foo", params := ["a"] }

/-- The verdict for an opaque type checked with the ambient alias `foo`. -/
def conCheckVerdictAgainstFooAlias (tc : TypeConstructor) (site : TypeConstructor.Site) : String :=
  match TypeConstructor.typeCheck tc site initTyContext envWithFooAlias with
  | .ok _ => "accepted"
  | .error e => toString (format e)

-- The program-site opaque-type check alone does not inspect aliases.
/-- info: "accepted" -/
#guard_msgs (whitespace := lax) in
#eval conCheckVerdictAgainstFooAlias fooTypeConstructor .program

-- The program-site check alone accepts a unary opaque type named after an ambient alias.
/-- info: "accepted" -/
#guard_msgs (whitespace := lax) in
#eval conCheckVerdictAgainstFooAlias fooTypeConstructorOneParam .program

-- A body-local opaque type cannot use an ambient alias name.
/-- info: "Local type 'foo' is already a type synonym" -/
#guard_msgs (whitespace := lax) in
#eval conCheckVerdictAgainstFooAlias fooTypeConstructor (.bodyLocal [])

-- An opaque type with a distinct name is accepted.
/-- info: "accepted" -/
#guard_msgs (whitespace := lax) in
#eval conCheckVerdictAgainstFooAlias { name := "bar", params := [] } .program

/-- Whether directly adding a known type after an alias permits the shared name. -/
def synonymThenAddKnownType : Except String (List String × Bool) :=
  match TEnv.addTypeAlias fooAlias initTyContext Lambda.TEnv.default with
  | .error e => .error (toString e)
  | .ok Env =>
    match initTyContext.addKnownTypeWithError
            { name := fooTypeConstructor.name, metadata := fooTypeConstructor.numargs }
            (Message.fromFormat f!"reserved") with
    | .error e => .error (toString (format e))
    | .ok C => .ok (Env.context.aliases.map (·.name), C.knownTypes.containsName "foo")

-- Direct known-type registration does not inspect aliases.
/-- info: Except.ok (["foo"], true) -/
#guard_msgs (whitespace := lax) in
#eval synonymThenAddKnownType

/-- Whether directly adding a datatype after an alias permits the shared name. -/
def synonymThenAddMutualBlock : Except String (List String × Bool) :=
  match TEnv.addTypeAlias fooAlias initTyContext Lambda.TEnv.default with
  | .error e => .error (toString e)
  | .ok Env =>
    match Core.MutualDatatype.typeCheck [fooDatatype] initTyContext Env with
    | .error e => .error (toString (format e))
    | .ok (_, C, Env) =>
      .ok (Env.context.aliases.map (·.name), C.knownTypes.containsName "foo")

-- The datatype check alone does not inspect aliases.
/-- info: Except.ok (["foo"], true) -/
#guard_msgs (whitespace := lax) in
#eval synonymThenAddMutualBlock

/-- Whether adding an alias after a known type permits the shared name. -/
def addKnownTypeThenSynonym : Except String (List String) :=
  match initTyContext.addKnownTypeWithError
          { name := fooTypeConstructor.name, metadata := fooTypeConstructor.numargs }
          (Message.fromFormat f!"reserved") with
  | .error e => .error (toString (format e))
  | .ok C =>
    match TEnv.addTypeAlias fooAlias C Lambda.TEnv.default with
    | .error e => .error (toString e)
    | .ok Env => .ok (Env.context.aliases.map (·.name))

-- An alias cannot reuse a known type name.
/-- info: Except.error "This type declaration's name is reserved!" -/
#guard_msgs (whitespace := lax) in
#eval addKnownTypeThenSynonym.mapError firstLine

/-- The verdict on adding a datatype named after a known type. -/
def addKnownTypeThenMutualBlock : String :=
  match initTyContext.addKnownTypeWithError
          { name := "foo", metadata := 0 } (Message.fromFormat f!"reserved") with
  | .error e => toString e
  | .ok C => match C.addMutualBlock [fooDatatype] with
             | .ok _ => "accepted"
             | .error e => firstLine (toString (format e))

-- A datatype whose name is a known type is refused.
/-- info: "Cannot name datatype same as known type!" -/
#guard_msgs (whitespace := lax) in
#eval addKnownTypeThenMutualBlock

end Core.AliasKnownTypeCollisionTests

end
