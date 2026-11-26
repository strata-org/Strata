/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LConstData
public import Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory

/-! # Datatype values in the evaluation of collection literals

The concrete evaluators of the `Map` and `Sequence` operations compute on literals
(`LConst.mapConst`, `LConst.sequenceConst`), whose elements are constants. A datatype value is an
expression, the application of a constructor to its arguments, so these evaluators do not apply to
a call whose arguments hold one. `extendDataLits F` wraps the evaluators of these operations in
the factory `F` so that they do:

- an argument that stands for a constant (`LExpr.toConst? F`), such as a constructor of `F`
  applied to constants, is passed to the evaluator as that constant, a datatype value
  (`LConst.dataConst`) when it is a constructor application;
- a result that is a datatype value whose constructors are those of `F` (`LConst.ctorsIn`) is
  turned back into the constructor application (`LConst.toLExpr`), so destructors and testers
  evaluate on it;
- a result that is the `ite` chain `select` returns at a key sort that is not canonical is
  decided, when the factory-aware equality of constants (`LConst.eqlIn`) decides each of its key
  comparisons;
- the map literal `update` returns at such a key sort keeps only the first of the entries whose
  keys `LConst.eqlIn` decides equal to the updated key.

The wrapped evaluator first tries the original one on the original arguments, so every result the
original gives is kept, up to these result transformations. The transformations apply only to a
result that type checks at the result type of the operator's annotation.

Key definitions: `dataLitsEval`, `dataLitsFunc`, `extendDataLits`. Their properties, and the
models of `extendDataLits F`, are in `Strata.Languages.Core.DataLitsProps`.
-/

namespace Core
open Lambda

public section

/-- Whether a function name is that of a `Map` or `Sequence` operation, whose evaluators compute
    on literals: `mapConst`, `select`, `update`, or a name starting with `Sequence.`. -/
@[expose] def isCollOpName (n : String) : Bool :=
  n == "mapConst" || n == "select" || n == "update" || n.startsWith "Sequence."

/-- Whether a factory function is a `Map` or `Sequence` operation (`isCollOpName`) or a
    monomorphic copy of one. -/
@[expose] def isCollOp (f : LFunc CoreLParams) : Bool :=
  isCollOpName f.name.name || (Strata.DL.Util.FuncAttr.findMonoCopyOf f.attr).any isCollOpName

/-- Whether a factory function is `update` or a monomorphic copy of it. -/
@[expose] def isUpdateOp (f : LFunc CoreLParams) : Bool :=
  f.name.name == "update" || Strata.DL.Util.FuncAttr.findMonoCopyOf f.attr == some "update"

/-- An argument passed as the constant it stands for (`LExpr.toConst? F`), with its metadata,
    when it stands for one. -/
@[expose] def dataLitsArg (F : @Lambda.Factory CoreLParams) (a : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  match a.toConst? F with
  | some c => .const a.metadata c
  | none => a

/-- A constant as an expression with metadata `m`: a well-typed datatype value whose constructors
    are those of `F` (`LConst.ctorsIn`) as the application of its constructor (`LConst.toLExpr`),
    any other constant as itself. -/
@[expose] def dataLitsConst (F : @Lambda.Factory CoreLParams) (m : CoreExprMetadata)
    (c : LConst) : LExpr CoreLParams.mono :=
  match c with
  | .dataConst .. => if c.wt && c.ctorsIn F then c.toLExpr m else .const m c
  | _ => .const m c

/-- The branch an `ite` chain over constant keys selects: `ite(key == k, t, f)` is `t` when
    `LConst.eqlIn F` decides the keys equal and the branch `f` selects when it decides them
    different; a constant closes the chain. `none` when a comparison on the way is undecided. -/
@[expose] def decideChain (F : @Lambda.Factory CoreLParams) :
    LExpr CoreLParams.mono → Option (LExpr CoreLParams.mono)
  | .ite _ (.eq _ (.const _ key) (.const _ k)) t f =>
    match LConst.eqlIn F key k with
    | some true => decideChain F t
    | some false => decideChain F f
    | none => none
  | .const m c => some (dataLitsConst F m c)
  | _ => none

/-- The entries of a map literal without the entries after the first whose keys `LConst.eqlIn F`
    decides equal to the first key: those entries are shadowed by the first. -/
@[expose] def dedupeFront (F : @Lambda.Factory CoreLParams) :
    List (LConst × LConst) → List (LConst × LConst)
  | [] => []
  | (k, v) :: rest => (k, v) :: rest.filter (fun e => LConst.eqlIn F k e.1 != some true)

/-- The result of an evaluator transformed for datatype values: a constant through
    `dataLitsConst`, after `dedupeFront` on the entries of a map literal at a key sort that is not
    canonical when `upd` holds (the function is `update`), and an `ite` chain through
    `decideChain` when it decides it. -/
@[expose] def dataLitsResult (F : @Lambda.Factory CoreLParams) (upd : Bool) :
    LExpr CoreLParams.mono → LExpr CoreLParams.mono
  | .const m (.mapConst k v d ⟨es⟩) =>
    if upd && !k.litCanonical then .const m (.mapConst k v d ⟨dedupeFront F es⟩)
    else .const m (.mapConst k v d ⟨es⟩)
  | .const m c => dataLitsConst F m c
  | r@(.ite ..) => (decideChain F r).getD r
  | r => r

/-- `dataLitsResult`, applied only to a result that type checks at the result type of the
    operator's annotation `ty` after `n` arguments. -/
@[expose] def dataLitsPost (F : @Lambda.Factory CoreLParams) (upd : Bool) (ty : Option LMonoTy)
    (n : Nat) (r : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  if ty.isSome && LExpr.typeCheck [] r == ty.map (LMonoTy.arrowResult n) then
    dataLitsResult F upd r
  else r

/-- The evaluator `ce` of a function with `n` inputs, extended to datatype values: the result `ce`
    gives on the arguments, else on the arguments passed as the constants they stand for
    (`dataLitsArg`), transformed by `dataLitsPost`. -/
@[expose] def dataLitsEval (F : @Lambda.Factory CoreLParams) (upd : Bool) (n : Nat)
    (ce : ConcreteEval CoreLParams) : ConcreteEval CoreLParams := fun md ty args =>
  ((ce md ty args).orElse fun _ => ce md ty (args.map (dataLitsArg F))).map
    (dataLitsPost F upd ty n)

/-- A function of `F` with its evaluator extended to datatype values (`dataLitsEval`), when it is
    a `Map` or `Sequence` operation (`isCollOp`) with an evaluator that is neither a constructor
    nor a short-circuit function; any other function as it is. -/
@[expose] def dataLitsFunc (F : @Lambda.Factory CoreLParams) (f : LFunc CoreLParams) :
    LFunc CoreLParams :=
  match f.concreteEval with
  | some ce =>
    if isCollOp f ∧ f.isConstr = false ∧
        Strata.DL.Util.FuncAttr.hasShortCircuit f.attr = false then
      { f with concreteEval := some (dataLitsEval F (isUpdateOp f) f.inputs.length ce) }
    else f
  | none => f

/-- The factory whose `Map` and `Sequence` evaluators also compute on datatype values: `F` with
    each function extended by `dataLitsFunc F`. Constructors are recognized as those of `F`. -/
@[expose] def extendDataLits (F : @Lambda.Factory CoreLParams) : @Lambda.Factory CoreLParams :=
  F.map (dataLitsFunc F) fun f => by unfold dataLitsFunc; split <;> (try split) <;> rfl

end -- public section
end Core
