/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.Languages.CoreMatch.DDMTransform.Grammar
public import Strata.Languages.CoreMatch.DDMTransform.StrataGen
public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.LExpr

/-!
Shared substrate for the rest of the translator: the `TransM` monad
and its state, scoped state combinators, and helpers that flatten
the DDM AST's cons-chain repetitions to plain `List`s.
-/

namespace Strata.CoreMatch.Translate

open Std (HashMap)
open Strata
open Lambda Imperative
open Lean.Parser

public section

open Strata.CoreMatchDDM

/-- Cached `(constructorName, [fieldName, …])` for one datatype. -/
abbrev DatatypeInfo := List (String × List String)

structure TransState where
  /-- Source file name, threaded into diagnostic source ranges. -/
  fileName : String := ""
  /-- DDM's flat symbol context, indexed by `FreeVarIndex`. -/
  gctx : GlobalContext := {}
  /-- For each entry of `gctx.vars`: `true` if it resolves as
  `LExpr.op` (function/constant), `false` for a term-level fvar.
  Computed once by `initFVarIsOp`. -/
  fvarIsOp : Array Bool := #[]
  /-- Type-level binders, innermost last. -/
  tyBVars : Array String := #[]
  /-- Term-level binders, innermost last. A slot holds either a
  pre-built reference (procedure input, let-bound variable) or an
  `LExpr.bvar 0` placeholder for a match-arm binder; `getBVarExpr`
  distinguishes the two cases. -/
  bvars : Array Core.Expression.Expr := #[]
  /-- Datatypes accumulated during the declaration walk. -/
  datatypes : HashMap String DatatypeInfo := {}
  /-- Counter for synthesised assert/assume/spec labels. -/
  labelCounter : Nat := 0
  /-- Names of functions in the enclosing `rec function` block.
  Self-references in their match arms get rewritten via
  `recRewrites`; empty outside such a block. -/
  recFns : List String := []
  /-- Maps `(recFnName, bottomRelativeFieldPos)` to the rec-result
  slot index in the case lambda. Consulted by `tryRecRewrite` to
  spot natural-style self-calls. -/
  recRewrites : HashMap (String × Nat) Nat := {}
  deriving Inhabited

abbrev TransM := StateT TransState (Except DiagnosticModel)

def mkIdent (name : String) : Core.Expression.Ident := ⟨name, ()⟩

def throwAt (range : SourceRange) (msg : String) : TransM α := do
  throw <| .withRange ⟨⟨(← StateT.get).fileName⟩, range⟩ msg

/-- Run `k` after mutating the field selected by `(get, set)`,
restoring the original value whether or not `k` throws. -/
def withSaved
    (get : TransState → β) (set : TransState → β → TransState) (mutate : β → β)
    (k : TransM α) : TransM α := do
  let old := get (← StateT.get)
  modify (set · (mutate old))
  try
    let result ← k
    modify (set · old)
    return result
  catch e =>
    modify (set · old)
    throw e

def withTypeBVars (xs : List String) : TransM α → TransM α :=
  withSaved (·.tyBVars) ({ · with tyBVars := · }) (· ++ xs.toArray)

def withBVarExprs (xs : Array Core.Expression.Expr) : TransM α → TransM α :=
  withSaved (·.bvars) ({ · with bvars := · }) (· ++ xs)

/-- Push binders that the body should reference as `LExpr.fvar`s
(procedure inputs, let-bound variables). -/
def withBVars (xs : List String) : TransM α → TransM α :=
  withBVarExprs (xs.toArray.map fun n => .fvar () (mkIdent n) none)

/-- Push binders that the body will reference as `LExpr.bvar`s, used
when the body will be wrapped in `absMulti` afterwards. The stored
`bvar 0` is just a tag; the real de Bruijn index is derived from the
slot's stack position by `getBVarExpr`. -/
def withBoundBVars (xs : List String) : TransM α → TransM α :=
  withBVarExprs (xs.toArray.map fun _ => .bvar () 0)

def withRecFns (fns : List String) : TransM α → TransM α :=
  withSaved (·.recFns) ({ · with recFns := · }) (fun _ => fns)

def withRecRewrites (entries : List ((String × Nat) × Nat))
    : TransM α → TransM α :=
  withSaved (·.recRewrites) ({ · with recRewrites := · }) fun m =>
    entries.foldl (fun m (k, v) => m.insert k v) m

def bindingsToList : Bindings SourceRange → List (Binding SourceRange)
  | .mkBindings _ ⟨_, xs⟩ => xs.toList

def bindingName : Binding SourceRange → String
  | .mkBinding _ ⟨_, n⟩ _
  | .outBinding _ ⟨_, n⟩ _
  | .inoutBinding _ ⟨_, n⟩ _
  | .casesBinding _ ⟨_, n⟩ _ => n

def constructorListToList :
    ConstructorList SourceRange → List (Constructor SourceRange)
  | .constructorListAtom _ c => [c]
  | .constructorListPush _ cs c => constructorListToList cs ++ [c]

def matchPatVarsToList :
    MatchPatVars SourceRange → List (MatchPatVar SourceRange)
  | .matchPatVars_nil _ => []
  | .matchPatVars_one _ v => [v]
  | .matchPatVars_cons _ vs v => matchPatVarsToList vs ++ [v]

def matchStmtArmsToList :
    MatchStmtArms SourceRange → List (MatchStmtArm SourceRange)
  | .matchStmtArms_nil _ => []
  | .matchStmtArms_cons _ a as => a :: matchStmtArmsToList as

def ctorFields : Constructor SourceRange → List (Binding SourceRange)
  | .constructor_mk _ _ ⟨_, none⟩ => []
  | .constructor_mk _ _ ⟨_, some ⟨_, fs⟩⟩ => fs.toList

end

end Strata.CoreMatch.Translate
