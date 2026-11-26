/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DataLits

meta section

/-! # Evaluation of collection operations on datatype values

Tests of `Core.extendDataLits` on `Core.Factory` extended with Laurel-like datatypes: `Field`
with the nullary constructors `F1` and `F2`, `$Box` with `BoxInt (intVal : int)`, and `Heap`
with `MkHeap (data : Map int (Map Field $Box), next : int)`. The `Map` operations of the extended
factory evaluate on datatype values; those of the factory without the extension do not. -/

namespace Core.DataLitsEvalTests

open Lambda

private def fieldT : LMonoTy := .tcons "Field" []
private def boxT : LMonoTy := .tcons "$Box" []
private def heapT : LMonoTy := .tcons "Heap" []
private def mapT (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]
private def arr (a b : LMonoTy) : LMonoTy := .tcons "arrow" [a, b]

private def fieldD : LDatatype Unit :=
  { name := "Field", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"F1", ()⟩, args := [] }, { name := ⟨"F2", ()⟩, args := [] }] }
private def boxD : LDatatype Unit :=
  { name := "$Box", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"BoxInt", ()⟩, args := [(⟨"intVal", ()⟩, .int)] }] }
private def heapArgs : List (Identifier Unit × LMonoTy) :=
  [(⟨"data", ()⟩, mapT .int (mapT fieldT boxT)), (⟨"next", ()⟩, .int)]
private def heapD : LDatatype Unit :=
  { name := "Heap", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"MkHeap", ()⟩, args := heapArgs }] }

/-- `Core.Factory` extended by the functions generated for `Field`, `$Box` and `Heap`. -/
private def base : Lambda.Factory CoreLParams :=
  (do
    let f ← Core.Factory.addFactory Lambda.Factory.default
    let f ← f.addFactory (← Lambda.genBlockFactory (T := CoreLParams) [fieldD])
    let f ← f.addFactory (← Lambda.genBlockFactory (T := CoreLParams) [boxD])
    f.addFactory (← Lambda.genBlockFactory (T := CoreLParams) [heapD])).toOption.getD default

/-- `base` with its `Map` and `Sequence` evaluators extended to datatype values. -/
private def fac : Lambda.Factory CoreLParams := extendDataLits base

private def opE (n : String) (ty : LMonoTy) : Expression.Expr := .op valueLoc ⟨n, ()⟩ (some ty)
private def app (f a : Expression.Expr) : Expression.Expr := .app valueLoc f a
private def int (i : Int) : Expression.Expr := .intConst valueLoc i
private def ev (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Expression.Expr :=
  (LExpr.eval 200 F default e).1
/-- The constant an expression is, if it is one. -/
private def constOf (e : Expression.Expr) : Option LConst :=
  match e with
  | .const _ c => some c
  | _ => none
/-- Equality up to metadata. -/
private def sameAs (a b : Expression.Expr) : Bool := a.eraseMetadata == b.eraseMetadata

private def boxInt (e : Expression.Expr) : Expression.Expr := app (opE "BoxInt" (arr .int boxT)) e
private def f1 : Expression.Expr := opE "F1" fieldT
private def f2 : Expression.Expr := opE "F2" fieldT
private def mapConstE (k v : LMonoTy) (d : Expression.Expr) : Expression.Expr :=
  app (opE "mapConst" (arr v (mapT k v))) d
private def selectE (k v : LMonoTy) (m i : Expression.Expr) : Expression.Expr :=
  app (app (opE "select" (arr (mapT k v) (arr k v))) m) i
private def updateE (k v : LMonoTy) (m i x : Expression.Expr) : Expression.Expr :=
  app (app (app (opE "update" (arr (mapT k v) (arr k (arr v (mapT k v))))) m) i) x

private def intS : LSort := .int
private def fieldS : LSort := .tcons "Field" []
private def boxS : LSort := .tcons "$Box" []
private def boxC (i : Int) : LConst := .dataConst "BoxInt" [intS] boxS #[.intConst i]
private def f1C : LConst := .dataConst "F1" [] fieldS #[]

/-! ## `mapConst` on a datatype value -/

#guard constOf (ev fac (mapConstE .int boxT (boxInt (int 8)))) =
  some (.mapConst intS boxS (boxC 8) #[])
#guard constOf (ev base (mapConstE .int boxT (boxInt (int 8)))) = none

/-! ## `update` and `select` on literals holding datatype values -/

/-- The map with default `BoxInt(0)` sending `F1` to `BoxInt(8)`. -/
private def inner : Expression.Expr :=
  updateE fieldT boxT (mapConstE fieldT boxT (boxInt (int 0))) f1 (boxInt (int 8))

#guard constOf (ev fac inner) = some (.mapConst fieldS boxS (boxC 0) #[(f1C, boxC 8)])
-- Updating `F1` again keeps one entry for it.
#guard constOf (ev fac (updateE fieldT boxT inner f1 (boxInt (int 9)))) =
  some (.mapConst fieldS boxS (boxC 0) #[(f1C, boxC 9)])
-- A select returns the constructor application of the value, or of the default.
#guard sameAs (ev fac (selectE fieldT boxT inner f1)) (boxInt (int 8))
#guard sameAs (ev fac (selectE fieldT boxT inner f2)) (boxInt (int 0))

/-- The `data` map of a heap: the map with the empty inner map as default, sending `-1` to
    `inner`. -/
private def dataE : Expression.Expr :=
  updateE .int (mapT fieldT boxT)
    (mapConstE .int (mapT fieldT boxT) (mapConstE fieldT boxT (boxInt (int 0)))) (int (-1)) inner

#guard constOf (ev fac dataE) =
  some (.mapConst intS (.tcons "Map" [fieldS, boxS]) (.mapConst fieldS boxS (boxC 0) #[])
    #[(.intConst (-1), .mapConst fieldS boxS (boxC 0) #[(f1C, boxC 8)])])

/-- `$Box..intVal!(select(select(Heap..data!(MkHeap(dataE, 0)), -1), f))`. -/
private def readE (f : Expression.Expr) : Expression.Expr :=
  let heap := app (app (opE "MkHeap" (arr (mapT .int (mapT fieldT boxT)) (arr .int heapT))) dataE)
    (int 0)
  let data := app (opE "Heap..data!" (arr heapT (mapT .int (mapT fieldT boxT)))) heap
  app (opE "$Box..intVal!" (arr boxT .int))
    (selectE fieldT boxT (selectE .int (mapT fieldT boxT) data (int (-1))) f)

#guard sameAs (ev fac (readE f1)) (int 8)
#guard sameAs (ev fac (readE f2)) (int 0)
#guard !sameAs (ev base (readE f1)) (int 8)

/-! ## Constants of constructor applications -/

#guard LExpr.toConst? base (LConst.toLExpr valueLoc (boxC 5) : Expression.Expr) = some (boxC 5)
-- An application whose operator is not a constructor stands for no constant.
#guard LExpr.toConst? base (app (opE "$Box..intVal!" (arr boxT .int)) (boxInt (int 5))) = none
#guard LExpr.toConst? base (app (opE "Int.Neg" (arr .int .int)) (int 5)) = none

end Core.DataLitsEvalTests
