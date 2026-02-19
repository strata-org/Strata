/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Laurel.Laurel
import Strata.DL.Lambda.LExpr

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LExpr)

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (types : List TypeDefinition) (name : Identifier) : List Identifier :=
  let rec go (fuel : Nat) (current : Identifier) : List Identifier :=
    match fuel with
    | 0 => [current]
    | fuel' + 1 =>
      current :: (types.foldl (fun acc td =>
        match td with
        | .Composite ct =>
          if ct.name == current then
            ct.extending.foldl (fun acc2 parent => acc2 ++ go fuel' parent) acc
          else acc
        | _ => acc) [])
  (go types.length name).eraseDups

/--
Collect all fields for a composite type, including inherited fields from parents.
-/
def collectAllFields (types : List TypeDefinition) (name : Identifier) : List Field :=
  let ancestors := computeAncestors types name
  -- Collect fields from all ancestors (parent fields first, then own fields)
  ancestors.reverse.foldl (fun acc ancestorName =>
    match types.findSome? (fun td => match td with
      | .Composite ct => if ct.name == ancestorName then some ct.fields else none
      | _ => none) with
    | some fields => acc ++ fields
    | none => acc) []

/--
Generate Core declarations for the type hierarchy:
- A UserType constant for each composite type
- A distinct declaration to ensure all UserType constants are different
- A `ancestorsFor<Type>` constant per composite type with the inner ancestor map
- A `ancestorsPerType` constant combining the per-type constants
-/
def generateTypeHierarchyDecls (types : List TypeDefinition) : List Core.Decl :=
  let composites := types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then [] else
  -- Generate a constant for each composite type
  let typeConstDecls := composites.map fun ct =>
    Core.Decl.func {
      name := Core.CoreIdent.glob (ct.name ++ "_UserType")
      typeArgs := []
      inputs := []
      output := .tcons "UserType" []
      body := none
    }
  -- Generate distinct declaration for all UserType constants
  let distinctExprs := composites.map fun ct =>
    LExpr.op () (Core.CoreIdent.glob (ct.name ++ "_UserType")) none
  -- Generate distinct declaration for all UserType constants (only if 2+ types)
  let distinctDecls := if distinctExprs.length >= 2 then
    [Core.Decl.distinct (Core.CoreIdent.unres "UserType_distinct") distinctExprs]
  else []
  -- Build a separate ancestorsFor<Type> constant for each composite type
  let userTypeTy := LMonoTy.tcons "UserType" []
  let innerMapTy := Core.mapTy userTypeTy .bool
  let outerMapTy := Core.mapTy userTypeTy innerMapTy
  -- Helper: build an inner map (Map UserType bool) for a given composite type
  -- Start with Map.empty(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : Core.Expression.Expr :=
    let ancestors := computeAncestors types ct.name
    let falseConst := LExpr.const () (.boolConst false)
    let emptyInner := LExpr.mkApp () Core.mapEmptyOp [falseConst]
    composites.foldl (fun acc otherCt =>
      let otherConst := LExpr.op () (Core.CoreIdent.glob (otherCt.name ++ "_UserType")) none
      let isAncestor := ancestors.contains otherCt.name
      let boolVal := LExpr.const () (.boolConst isAncestor)
      LExpr.mkApp () Core.mapUpdateOp [acc, otherConst, boolVal]
    ) emptyInner
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls := composites.map fun ct =>
    Core.Decl.func {
      name := Core.CoreIdent.unres (s!"ancestorsFor{ct.name}")
      typeArgs := []
      inputs := []
      output := innerMapTy
      body := some (mkInnerMap ct)
    }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := LExpr.const () (.boolConst false)
  let emptyInner := LExpr.mkApp () Core.mapEmptyOp [falseConst]
  let emptyOuter := LExpr.mkApp () Core.mapEmptyOp [emptyInner]
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := LExpr.op () (Core.CoreIdent.glob (ct.name ++ "_UserType")) none
    let innerMapRef := LExpr.op () (Core.CoreIdent.unres (s!"ancestorsFor{ct.name}")) (some innerMapTy)
    LExpr.mkApp () Core.mapUpdateOp [acc, typeConst, innerMapRef]
  ) emptyOuter
  -- Generate ancestorsPerType as a 0-ary function (constant) combining the per-type constants
  let ancestorsDecl := Core.Decl.func {
    name := Core.CoreIdent.unres "ancestorsPerType"
    typeArgs := []
    inputs := []
    output := outerMapTy
    body := some outerMapExpr
  }
  typeConstDecls ++ distinctDecls ++ ancestorsForDecls ++ [ancestorsDecl]

end Laurel
