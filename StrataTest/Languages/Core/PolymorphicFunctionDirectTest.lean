/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprT

/-!
# Direct Lambda Typechecker Test for Polymorphic Function Issue

This test directly calls the Lambda typechecker (LExpr.resolve) on the exact
LExpr term and TEnv state that causes the failure in PolymorphicFunctionTest Test 9.

Debug output from Boogie typechecker:
  LExpr: (((~makePair : (arrow a (arrow b (Map a b)))) ((~identity : (arrow a a)) #42)) ((~identity : (arrow a a)) #true))
  TEnv.subst: [($__ty3, (Map int bool))] []
  TEnv.context.types: [(init_m_0, $__ty3) (m, (Map int bool))]
-/

namespace Lambda.PolymorphicFunctionDirectTest

open Std (ToFormat Format format)
open LTy LExpr.SyntaxMono LExpr LMonoTy

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

-- Create the factory with identity and makePair functions
-- IMPORTANT: typeArgs is EMPTY but the types use $__ty0, $__ty1, $__ty2
-- This is the bug - the type variables are not being freshened because typeArgs is empty!
private def testPolyFns : (@Factory TestParams) :=
  #[{ name := "identity",
      typeArgs := [],  -- Empty! This is the bug.
      inputs := [("x", .ftvar "$__ty0")],
      output := .ftvar "$__ty0"},
    { name := "makePair",
      typeArgs := [],  -- Empty! This is the bug.
      inputs := [("x", .ftvar "$__ty1"), ("y", .ftvar "$__ty2")],
      output := .tcons "Map" [.ftvar "$__ty1", .ftvar "$__ty2"]}
  ]

private def testKnownTypes : KnownTypes :=
  KnownTypes.default.insert "Map" 2

private def testContext : LContext TestParams :=
  { LContext.default with functions := testPolyFns, knownTypes := testKnownTypes }

-- Build the exact LExpr from debug output:
-- (((~makePair : (arrow a (arrow b (Map a b)))) ((~identity : (arrow a a)) #42)) ((~identity : (arrow a a)) #true))
private def failingExpr : LExpr TestParams.mono :=
  let identityTy : LMonoTy := .tcons "arrow" [.ftvar "a", .ftvar "a"]
  let makePairTy : LMonoTy := .tcons "arrow" [.ftvar "a", .tcons "arrow" [.ftvar "b", .tcons "Map" [.ftvar "a", .ftvar "b"]]]
  let makePairOp : LExpr TestParams.mono := .op () "makePair" (some makePairTy)
  let identityOp : LExpr TestParams.mono := .op () "identity" (some identityTy)
  let int42 : LExpr TestParams.mono := .const () (.intConst 42)
  let boolTrue : LExpr TestParams.mono := .const () (.boolConst true)
  let identity42 : LExpr TestParams.mono := .app () identityOp int42
  let identityTrue : LExpr TestParams.mono := .app () identityOp boolTrue
  let makePairApp1 : LExpr TestParams.mono := .app () makePairOp identity42
  let makePairApp2 : LExpr TestParams.mono := .app () makePairApp1 identityTrue
  makePairApp2

-- Create the exact TEnv from debug output:
-- TEnv.subst: [($__ty3, (Map int bool))] []  (two scopes)
-- TEnv.context.types: [(init_m_0, $__ty3) (m, (Map int bool))]
-- TEnv.genState.tyGen: 4
-- TEnv.genState.tyPrefix: $__ty
private def testEnv : TEnv Unit :=
  let mapIntBool : LMonoTy := .tcons "Map" [.tcons "int" [], .tcons "bool" []]
  { genEnv := {
      context := { types := [[("init_m_0", .forAll [] (.ftvar "$__ty3")), ("m", .forAll [] mapIntBool)]] }
      genState := { tyGen := 4, tyPrefix := "$__ty" }
    }
    stateSubstInfo := {
      subst := [[("$__ty3", mapIntBool)], []]
      isWF := by rfl
    }
  }

-- Test that calling LExpr.resolve on this expression fails with the unification error
/--
info: error: Impossible to unify (arrow $__ty0 $__ty0) with (arrow bool $__ty14).
First mismatch: int with bool.
-/
#guard_msgs in
#eval do
  let ans ← LExpr.resolve (T:=TestParams) testContext testEnv failingExpr
  return (format ans)

end Lambda.PolymorphicFunctionDirectTest
