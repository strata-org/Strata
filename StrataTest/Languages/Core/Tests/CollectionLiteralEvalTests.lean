/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Factory

meta section

/-! # Tests for the map and sequence literal evaluators

Unit tests for the evaluators of `Core.AggregateLitEval`, which `Core.Factory`'s `Map` and
`Sequence` operations run on literal arguments. -/

namespace Core.CollectionLiteralEvalTests

open Lambda

private def intS : LSort := .tcons "int" []

/-- The `Map int int` literal with default `0` and the given entries. -/
private def intMap (es : Array (Int × Int)) : LConst :=
  .mapConst intS intS (.intConst 0) (es.map fun (k, v) => (.intConst k, .intConst v))

/-- The `Sequence int` literal with the given elements. -/
private def intSeq (xs : Array Int) : LConst := .sequenceConst intS (xs.map .intConst)

private def mapTy (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]
private def seqTy (a : LMonoTy) : LMonoTy := .tcons "Sequence" [a]

/-! ## Map literals -/

-- `mapConst` reads the key and value sorts from the operator type.
#guard AggregateLitEval.mapConst (some (.arrow .int (mapTy .int .int))) [.intConst 0] =
  some (intMap #[])
-- Without an operator type it declines.
#guard AggregateLitEval.mapConst none [.intConst 0] = none
-- With a default of the wrong sort it builds a literal that is not well typed, which
-- `polyLitOp` rejects.
#guard (AggregateLitEval.mapConst (some (.arrow .int (mapTy .int .int))) [.boolConst true]).map
  LConst.wt = some false
-- So the factory function declines the call.
#guard (mapConstFunc.func.concreteEval.bind fun ev =>
  ev valueLoc (some (.arrow .int (mapTy .int .int))) [.boolConst valueLoc true]).isNone
-- With a default of the value sort, it returns the empty map literal.
#guard (match mapConstFunc.func.concreteEval.bind fun ev =>
    ev valueLoc (some (.arrow .int (mapTy .int .int))) [.intConst valueLoc 0] with
  | some (.const _ c) => some c
  | _ => none) = some (intMap #[])
-- A non-ground annotation is declined, even when the key and value sorts are ground.
#guard AggregateLitEval.mapConst (some (.arrow .int (mapTy (.ftvar "k") .int))) [.intConst 0] = none
#guard AggregateLitEval.mapConst (some (.arrow (.ftvar "v") (mapTy .int .int))) [.intConst 0] = none

-- An update appends the new entry; updating a key again replaces its entry.
#guard AggregateLitEval.mapUpdate none [intMap #[], .intConst 1, .intConst 10] =
  some (intMap #[(1, 10)])
#guard AggregateLitEval.mapUpdate none [intMap #[(1, 10), (2, 20)], .intConst 1, .intConst 30] =
  some (intMap #[(2, 20), (1, 30)])
-- Setting a key to the default drops its entry.
#guard AggregateLitEval.mapUpdate none [intMap #[(1, 10)], .intConst 1, .intConst 0] =
  some (intMap #[])

-- A select returns the key's value, or the default for a key without an entry.
#guard AggregateLitEval.mapSelect none [intMap #[(1, 10), (2, 20)], .intConst 2]
  = some (.intConst 20)
#guard AggregateLitEval.mapSelect none [intMap #[(1, 10)], .intConst 3] = some (.intConst 0)

/-- The literal `mapSelectFunc`'s concrete evaluator, the one the verifier and both interpreters
    run through `polyLitOp`, returns for `select(intMap es, k)` at the operator annotation `ty`. -/
private def factorySelect (ty : Option LMonoTy) (es : Array (Int × Int)) (k : Int) :
    Option LConst :=
  match mapSelectFunc.func.concreteEval.bind fun ev =>
      ev valueLoc ty [.const valueLoc (intMap es), .intConst valueLoc k] with
  | some (.const _ c) => some c
  | _ => none

-- Through `polyLitOp`, the call evaluates at its instantiated annotation...
#guard factorySelect (some (.arrow (mapTy .int .int) (.arrow .int .int))) #[(1, 10)] 1 =
  some (.intConst 10)
-- ...but declines without an annotation, although `AggregateLitEval.mapSelect` answers there,
#guard factorySelect none #[(1, 10)] 1 = none
-- and declines at an annotation whose result type is not the literal's.
#guard factorySelect (some (.arrow (mapTy .int .int) (.arrow .int .bool))) #[(1, 10)] 1 = none

-- Keys of a sort containing `Map` are not compared, so select and update decline.
private def mapKeyed : LConst :=
  .mapConst (.tcons "Map" [intS, intS]) intS (.intConst 0) #[]
#guard AggregateLitEval.mapSelect none [mapKeyed, intMap #[]] = none
#guard AggregateLitEval.mapUpdate none [mapKeyed, intMap #[], .intConst 1] = none

/-! ## Sequence literals -/

#guard AggregateLitEval.seqEmpty (some (seqTy .int)) [] = some (intSeq #[])
#guard AggregateLitEval.seqEmpty none [] = none
#guard AggregateLitEval.seqEmpty (some (seqTy (.ftvar "a"))) [] = none
#guard AggregateLitEval.seqLength none [intSeq #[1, 2, 3]] = some (.intConst 3)
#guard AggregateLitEval.seqAppend none [intSeq #[1], intSeq #[2, 3]] = some (intSeq #[1, 2, 3])
#guard AggregateLitEval.seqBuild none [intSeq #[1], .intConst 2] = some (intSeq #[1, 2])
#guard AggregateLitEval.seqContains none [intSeq #[1, 2], .intConst 2] = some (.boolConst true)
#guard AggregateLitEval.seqContains none [intSeq #[1, 2], .intConst 3] = some (.boolConst false)

-- Indexed operations evaluate in bounds and decline out of bounds.
#guard AggregateLitEval.seqSelect none [intSeq #[1, 2], .intConst 1] = some (.intConst 2)
#guard AggregateLitEval.seqSelect none [intSeq #[1, 2], .intConst 2] = none
#guard AggregateLitEval.seqSelect none [intSeq #[1, 2], .intConst (-1)] = none
#guard AggregateLitEval.seqUpdate none [intSeq #[1, 2], .intConst 0, .intConst 5] =
  some (intSeq #[5, 2])
#guard AggregateLitEval.seqUpdate none [intSeq #[1, 2], .intConst 2, .intConst 5] = none
#guard AggregateLitEval.seqTake none [intSeq #[1, 2, 3], .intConst 2] = some (intSeq #[1, 2])
#guard AggregateLitEval.seqTake none [intSeq #[1, 2, 3], .intConst 4] = none
#guard AggregateLitEval.seqDrop none [intSeq #[1, 2, 3], .intConst 1] = some (intSeq #[2, 3])
#guard AggregateLitEval.seqDrop none [intSeq #[1, 2, 3], .intConst (-1)] = none

-- Elements of a sort containing `Map` are not compared, so `contains` declines.
private def seqOfMaps : LConst := .sequenceConst (.tcons "Map" [intS, intS]) #[intMap #[]]
#guard AggregateLitEval.seqContains none [seqOfMaps, intMap #[]] = none

/-! ## Size bound

Through `polyLitOp`, a result of more than `maxLitSize` constants is declined. -/

/-- The literal `seqAppendFunc`'s concrete evaluator returns for `Sequence.append(s, t)`. -/
private def factoryAppend (s t : Array Int) : Option LConst :=
  match seqAppendFunc.func.concreteEval.bind fun ev =>
      ev valueLoc (some (.arrow (seqTy .int) (.arrow (seqTy .int) (seqTy .int))))
        [.const valueLoc (intSeq s), .const valueLoc (intSeq t)] with
  | some (.const _ c) => some c
  | _ => none

#guard maxLitSize = 64
-- `intSeq` of 63 elements has 64 constants, so it is returned...
#guard factoryAppend (Array.range 31 |>.map Int.ofNat) (Array.range 32 |>.map Int.ofNat) =
  some (intSeq ((Array.range 31 ++ Array.range 32).map Int.ofNat))
-- ...but one of 64 elements is declined, although `AggregateLitEval.seqAppend` builds it.
#guard factoryAppend (Array.range 32 |>.map Int.ofNat) (Array.range 32 |>.map Int.ofNat) = none
#guard (AggregateLitEval.seqAppend none [intSeq (Array.range 32 |>.map Int.ofNat),
  intSeq (Array.range 32 |>.map Int.ofNat)]).map LConst.size = some 65

end Core.CollectionLiteralEvalTests
