/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DL.Lambda.LExprEval
-- import Strata.DL.Lambda.LExprType
import Strata.DL.Bounded.BExpr

namespace Bounded

open Std (ToFormat Format format)
open Lambda

/-! # Bounded Dialect

The Bounded dialect is an extension of Lambda (see `Strata.DL.Lambda`) with support for bounded integer types. See `Stata.DL.Bounded.BExpr` for the translation from Bounded to Lambda.
-/

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier] [Coe String Identifier]

def translateBoundedLMonoTySignature (L: @LMonoTySignature Identifier BoundTyRestrict) : @LMonoTySignature Identifier Empty :=
  L.map (fun (x, y) => (x, removeTyBound y))

--TODO: translate TGenEnv (can do bc no factory)

-- TODO: translate body and axioms to LExprT

private structure LFuncT (Identifier : Type) (ExtraRestrict: Type)  where
  name     : Identifier
  typeArgs : List TyIdentifier := []
  inputs   : @LMonoTySignature Identifier ExtraRestrict
  output   : LMonoTy ExtraRestrict
  body     : Option (LExprT Identifier ExtraRestrict) := .none
  attr     : Array String := #[]
  -- TODO: what should be tye of concreteEval?
  concreteEval : Option ((LExpr (LMonoTy ExtraRestrict) Identifier) → List (LExpr (LMonoTy ExtraRestrict) Identifier) → (LExpr (LMonoTy ExtraRestrict) Identifier)) := .none
  axioms   : List (LExprT Identifier ExtraRestrict) := []

def LFunc.toLFuncT [DecidableEq ExtraRestrict] (L: LFunc Identifier ExtraRestrict) (T: TEnv Identifier ExtraRestrict) : Except Format (LFuncT Identifier ExtraRestrict × TEnv Identifier ExtraRestrict) := do
  let (b, T1) ←  match L.body with
  | some b =>
    let (b1, T1) ← LExprT.fromLExpr T b;
    .ok (some b1, T1)
  | none => .ok (none, T);
  let (l, T) ← List.foldlM (fun (l1, T) e => do
    let (e, T) ← LExprT.fromLExpr T e;
    .ok (e :: l1, T)) ([], T1) L.axioms;
  .ok ({name := L.name, typeArgs := L.typeArgs, inputs := L.inputs, output := L.output, body :=b, attr := L.attr, concreteEval := L.concreteEval, axioms := l}, T)

def LFuncT.translateBounded (L: LFuncT Identifier BoundTyRestrict) (T: TGenEnv Identifier BoundTyRestrict) : (LFuncT Identifier Empty × List (LExprT Identifier Empty) × TGenEnv Identifier BoundTyRestrict) :=
  let (newBody, bodyWf, T) := match L.body with
  | some b =>
    let (b, wf, T) := translateAndWfBounded T b;
    (some b, wf, T)
  | none => (none, [], T);
  let (newAx, axWf, T) := List.foldl (fun (ax, wf, T) e =>
    let (ax1, wf1, T1) := translateAndWfBounded T e;
    (ax1 :: ax, wf1 ++ wf, T1)) ([], [], T) L.axioms;
  ({name := L.name, typeArgs := L.typeArgs, inputs := translateBoundedLMonoTySignature L.inputs, output := removeTyBound L.output, body :=newBody, attr := L.attr, concreteEval := .none, axioms := newAx}, bodyWf ++ axWf, T) -- TODO: fix concrete eval

def LFuncT.toLFunc (L: LFuncT Identifier ExtraRestrict) : LFunc Identifier ExtraRestrict :=
  {name := L.name, typeArgs := L.typeArgs, inputs := L.inputs, output := L.output, body :=L.body.map LExprT.toLExpr, attr := L.attr, concreteEval := L.concreteEval, axioms := L.axioms.map LExprT.toLExpr}

/--
translateBoundedLFunc removes bounded types from an LFunc and generates additional well-formedness conditions for the function bodies.

TODO: ignores concreteEval
-/
def LFunc.translateBounded (L: LFunc Identifier BoundTyRestrict) (T: TEnv Identifier BoundTyRestrict) : Except Format (LFunc Identifier Empty × List (LExprT Identifier Empty) × TEnv Identifier BoundTyRestrict) := do
  let (L, T) ← LFunc.toLFuncT L T;
  let (L1, wf, G) := LFuncT.translateBounded L T.toTGenEnv;
  let T := T.updateGenEnv G;
  .ok (LFuncT.toLFunc L1, wf, T)

-- Translate Factory (Note: includes TEnv which has factory, we will change this later but shouldnt actually use the factory since everything is already typechecked)
def Factory.translateBounded (F: @Factory Identifier BoundTyRestrict) (T: TEnv Identifier BoundTyRestrict) : Except Format (@Factory Identifier Empty × List (LExprT Identifier Empty) × TEnv Identifier BoundTyRestrict) :=
-- need to carry around index
  Array.foldlM (fun (a, wf, T) (L, i) => do
    let (L1, wf1, T1) ← LFunc.translateBounded L T;
    .ok (Array.setIfInBounds a i L1, wf1 ++ wf, T1)
    ) (Array.emptyWithCapacity (Array.size F), [], T) (Array.zip F (Array.range (Array.size F)))
