/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Term
public import Strata.DL.SMT.Op
public import Strata.DL.SMT.Factory

/-!
# Array Axiomatization

This module provides a transformation from SMT-IR that uses the built-in array
theory (`Op.select`/`Op.store` with `Array` types) to an equivalent
axiomatization using uninterpreted functions and explicit axioms.

When the `useArrayTheory` option is `false`, this pass is applied after SMT
encoding to replace:
- `TermType.constr "Array" [A, B]` → `TermType.constr "Map" [A, B]`
- `Op.select` → UF `select` (per `(A, B)` instance)
- `Op.store`  → UF `update` (per `(A, B)` instance)

and adds the standard read-over-write axioms for each `(A, B)` pair found
in the problem.
-/

public section

namespace Strata.SMT.ArrayAxiom
open Strata.SMT

/-- Replace all `Array` type constructors with `Map` in a `TermType`. -/
def replaceArrayType : TermType → TermType
  | .constr "Array" args => .constr "Map" (args.map replaceArrayType)
  | .constr id args => .constr id (args.map replaceArrayType)
  | .option ty => .option (replaceArrayType ty)
  | ty => ty

/-- Replace `Array` types in a UF signature. -/
def replaceArrayTypeInUF (uf : UF) : UF :=
  { uf with
    args := uf.args.map fun v => { v with ty := replaceArrayType v.ty }
    out := replaceArrayType uf.out }

/-- Create a `select` UF for `Map A B`: `(Map A B, A) → B`. -/
def mkSelectUF (tyA tyB : TermType) : UF :=
  let mapTy := TermType.constr "Map" [tyA, tyB]
  { id := "select", args := [⟨"m", mapTy⟩, ⟨"i", tyA⟩], out := tyB }

/-- Create an `update` UF for `Map A B`: `(Map A B, A, B) → Map A B`. -/
def mkUpdateUF (tyA tyB : TermType) : UF :=
  let mapTy := TermType.constr "Map" [tyA, tyB]
  { id := "update", args := [⟨"m", mapTy⟩, ⟨"i", tyA⟩, ⟨"x", tyB⟩], out := mapTy }

/-- Replace Array operations and types in a term.
    `Op.select` → UF `select`, `Op.store` → UF `update`,
    `Array` type constructors → `Map`. -/
def replaceArraysInTerm : Term → Term
  | .prim p => .prim p
  | .var v => .var { v with ty := replaceArrayType v.ty }
  | .none ty => .none (replaceArrayType ty)
  | .some t => .some (replaceArraysInTerm t)
  | .app (.arr .select) args retTy =>
    let args' := args.map replaceArraysInTerm
    let retTy' := replaceArrayType retTy
    match args' with
    | [m', k'] =>
      match m'.typeOf with
      | .constr "Map" [tyA, tyB] =>
        .app (.uf (mkSelectUF tyA tyB)) [m', k'] retTy'
      | _ => .app Op.select args' retTy'
    | _ => .app Op.select args' retTy'
  | .app (.arr .store) args retTy =>
    let args' := args.map replaceArraysInTerm
    let retTy' := replaceArrayType retTy
    match args' with
    | [m', k', v'] =>
      match m'.typeOf with
      | .constr "Map" [tyA, tyB] =>
        .app (.uf (mkUpdateUF tyA tyB)) [m', k', v'] retTy'
      | _ => .app Op.store args' retTy'
    | _ => .app Op.store args' retTy'
  | .app op args retTy =>
    let args' := args.map replaceArraysInTerm
    let retTy' := replaceArrayType retTy
    let op' := match op with
      | .core (.uf uf) => .core (.uf (replaceArrayTypeInUF uf))
      | op => op
    .app op' args' retTy'
  | .quant qk vars tr body =>
    let vars' := vars.map fun v => { v with ty := replaceArrayType v.ty }
    .quant qk vars' (replaceArraysInTerm tr) (replaceArraysInTerm body)

/-- Collect unique `(A, B)` type pairs from `Array A B` occurrences in a type. -/
def collectArrayPairsFromType (ty : TermType)
    (acc : List (TermType × TermType)) : List (TermType × TermType) :=
  match ty with
  | .constr "Array" [a, b] =>
    let pair := (a, b)
    let acc := if acc.any (· == pair) then acc else pair :: acc
    let acc := collectArrayPairsFromType a acc
    collectArrayPairsFromType b acc
  | .constr _ args => args.foldl (fun acc arg => collectArrayPairsFromType arg acc) acc
  | .option ty => collectArrayPairsFromType ty acc
  | _ => acc

/-- Collect unique `(A, B)` type pairs from `Array` types appearing in a term. -/
def collectArrayPairsFromTerm (t : Term)
    (acc : List (TermType × TermType)) : List (TermType × TermType) :=
  match t with
  | .prim _ => acc
  | .var v => collectArrayPairsFromType v.ty acc
  | .none ty => collectArrayPairsFromType ty acc
  | .some t => collectArrayPairsFromTerm t acc
  | .app op args retTy =>
    let acc := collectArrayPairsFromType retTy acc
    let acc := match op with
      | .core (.uf uf) =>
        let acc := uf.args.foldl (fun acc v => collectArrayPairsFromType v.ty acc) acc
        collectArrayPairsFromType uf.out acc
      | _ => acc
    args.foldl (fun acc arg => collectArrayPairsFromTerm arg acc) acc
  | .quant _ vars tr body =>
    let acc := vars.foldl (fun acc v => collectArrayPairsFromType v.ty acc) acc
    let acc := collectArrayPairsFromTerm tr acc
    collectArrayPairsFromTerm body acc

/-- Check whether `Op.store` appears in a term (i.e., whether the problem uses array updates). -/
def hasStoreOp : Term → Bool
  | .app (.arr .store) _ _ => true
  | .app _ args _ => args.attach.any fun ⟨t, _⟩ => hasStoreOp t
  | .some t => hasStoreOp t
  | .quant _ _ tr body => hasStoreOp tr || hasStoreOp body
  | _ => false

/-- Generate `select`/`update` UFs and read-over-write axioms for a `(A, B)` pair.

    When `needsStore` is `false` (i.e., no `store` operations appear for this type
    pair), only the `select` UF is generated with no axioms — matching the behavior
    of the original factory-based encoding.

    Axioms (generated only when `needsStore = true`):
    - **updateSelect**: `∀m k v. select(update(m, k, v), k) = v`
    - **updatePreserve**: `∀m k' k v. k' = k ∨ select(update(m, k, v), k') = select(m, k')` -/
def generateArrayAxioms (tyA tyB : TermType) (needsStore : Bool) : Array UF × Array Term :=
  let selectUF := mkSelectUF tyA tyB
  if !needsStore then
    (#[selectUF], #[])
  else
    let mapTy := TermType.constr "Map" [tyA, tyB]
    let updateUF := mkUpdateUF tyA tyB

    -- Bound variables for axioms (using $__ax prefix to avoid clashes)
    let m := TermVar.mk "$__ax_m" mapTy
    let k := TermVar.mk "$__ax_k" tyA
    let k' := TermVar.mk "$__ax_k'" tyA
    let v := TermVar.mk "$__ax_v" tyB

    -- updateSelect: ∀m:Map(A,B), k:A, v:B. select(update(m, k, v), k) = v
    let updateTerm := Term.app (.uf updateUF) [.var m, .var k, .var v] mapTy
    let selectOfUpdate := Term.app (.uf selectUF) [updateTerm, .var k] tyB
    let trigger := Term.app .triggers [selectOfUpdate] .trigger
    let updateSelectAxiom := Term.quant .all [m, k, v] trigger
      (Factory.eq selectOfUpdate (.var v))

    -- updatePreserve: ∀m k' k v. k' = k ∨ select(update(m, k, v), k') = select(m, k')
    let updateTerm2 := Term.app (.uf updateUF) [.var m, .var k, .var v] mapTy
    let selectOfUpdate2 := Term.app (.uf selectUF) [updateTerm2, .var k'] tyB
    let selectOriginal := Term.app (.uf selectUF) [.var m, .var k'] tyB
    let keysEqual := Factory.eq (.var k') (.var k)
    let preserveTrigger := Term.app .triggers [selectOfUpdate2] .trigger
    let updatePreserveAxiom := Term.quant .all [m, k', k, v]
      preserveTrigger
      (Factory.ite keysEqual (Term.bool true)
        (Factory.eq selectOfUpdate2 selectOriginal))

    (#[selectUF, updateUF], #[updateSelectAxiom, updatePreserveAxiom])

/-- Result of the `axiomatizeArrays` transformation. -/
structure AxiomatizeResult where
  /-- All UFs (existing with replaced types + new select/update UFs). -/
  ufs : Array UF
  /-- Interpreted function pairs (UF with replaced types, transformed body). -/
  ifs : Array (UF × Term)
  /-- All axioms (existing transformed + new array axioms). -/
  axioms : Array Term
  /-- Transformed assumption terms. -/
  assumptions : List Term
  /-- Transformed conclusion term. -/
  conclusion : Term
  /-- Whether any `Array` types were found (caller should declare `Map` sort). -/
  hasArrayTypes : Bool

/-- Transform an SMT problem from array-theory encoding to UF axiomatization.

    Replaces `Array` types with `Map` sorts, `Op.select`/`Op.store` with
    uninterpreted functions, and generates read-over-write axioms for each
    `(A, B)` type pair found in the problem.

    This is a pure function operating on SMT-IR components. The caller is
    responsible for integrating the result back into the verification context
    (e.g. declaring the `Map` sort). -/
def axiomatizeArrays
    (ufs : Array UF)
    (ifPairs : Array (UF × Term))
    (axioms : Array Term)
    (assumptions : List Term)
    (conclusion : Term)
    : AxiomatizeResult := Id.run do
  -- 1. Collect all (A, B) type pairs from Array types across the problem
  let allTerms := axioms.toList ++ (ifPairs.toList.map (·.2)) ++ assumptions ++ [conclusion]
  let allUFs := ufs.toList ++ (ifPairs.toList.map (·.1))
  let mut pairs : List (TermType × TermType) := []
  for t in allTerms do
    pairs := collectArrayPairsFromTerm t pairs
  for uf in allUFs do
    for v in uf.args do
      pairs := collectArrayPairsFromType v.ty pairs
    pairs := collectArrayPairsFromType uf.out pairs

  if pairs.isEmpty then
    return { ufs, ifs := ifPairs, axioms, assumptions, conclusion, hasArrayTypes := false }

  -- 2. Check whether store operations appear (needed for axiom generation)
  let storeUsed := allTerms.any hasStoreOp

  -- 3. Replace Array→Map in all existing components
  let ufs' := ufs.map replaceArrayTypeInUF
  let ifPairs' := ifPairs.map fun (uf, body) => (replaceArrayTypeInUF uf, replaceArraysInTerm body)
  let axioms' := axioms.map replaceArraysInTerm
  let assumptions' := assumptions.map replaceArraysInTerm
  let conclusion' := replaceArraysInTerm conclusion

  -- 4. Generate axioms and UFs for each (A, B) pair
  --    Replace Array→Map in collected pairs too (handles nested maps).
  let pairs' := pairs.map fun (a, b) => (replaceArrayType a, replaceArrayType b)
  -- Deduplicate after replacement
  let mut uniquePairs : List (TermType × TermType) := []
  for p in pairs' do
    if !uniquePairs.any (· == p) then
      uniquePairs := uniquePairs ++ [p]
  let mut newUFs : Array UF := #[]
  let mut newAxioms : Array Term := #[]
  for (tyA, tyB) in uniquePairs do
    let (pairUFs, pairAxioms) := generateArrayAxioms tyA tyB storeUsed
    for uf in pairUFs do
      if !newUFs.contains uf && !ufs'.contains uf then
        newUFs := newUFs.push uf
    for ax in pairAxioms do
      newAxioms := newAxioms.push ax

  { ufs := ufs' ++ newUFs
    ifs := ifPairs'
    axioms := axioms' ++ newAxioms
    assumptions := assumptions'
    conclusion := conclusion'
    hasArrayTypes := true }

end Strata.SMT.ArrayAxiom
end
