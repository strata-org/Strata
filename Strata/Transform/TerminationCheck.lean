/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.DL.Lambda.AdtRankAxioms
public import Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.PipelinePhase

/-! # Termination Checking for Recursive Functions

This transformation generates termination-checking procedures for recursive
function blocks. For each `recFuncBlock`, it:

1. Generates `D..adtRank` UF declarations and per-constructor axioms for the
   datatypes used as decreasing measures.
2. Generates a `$$term` procedure per function that asserts `adtRank` decreases
   at each recursive call site.
-/

public section

namespace Core
namespace TermCheck

open Lambda
open Strata (DiagnosticModel)
open Strata.DL.Util (FuncAttr)
open Core.Transform

/-- Statistics keys tracked by the termination checking transformation. -/
inductive Stats where
  | termCheckProcsGenerated
  | termCheckAssertsEmitted
  | adtRankAxiomsGenerated

#derive_prefixed_toString Stats "TermCheck"

/-- Suffix for generated termination-checking procedures. -/
def termSuffix : String := "$$term"

def termProcName (name : String) : String := s!"{name}{termSuffix}"

def isTermProc (name : String) : Bool := name.endsWith termSuffix

/-- Find the decreasing parameter index for a function: explicit `measure`
    (from `decreases` clause), or fallback to `@[cases]` (`inlineIfConstr`). -/
private def getDecreasesIdx (func : Function) : Option Nat :=
  match func.measure with
  | some (.fvar _ id _) => func.inputs.keys.findIdx? (· == id)
  | some _ => none
  | none => FuncAttr.findInlineIfConstr func.attr

/-- Extract the datatype name from a monomorphic type. -/
private def adtNameOf (ty : LMonoTy) : String :=
  match ty with
  | .tcons n _ => n
  | _ => ""

/-- Build the `adtRank(callArg) < adtRank(callerParam)` expression. -/
private def mkAdtRankLt
    (callArg : Expression.Expr)
    (callerParam : Expression.Ident)
    (callerAdtTy calleeAdtTy : LMonoTy)
    : Expression.Expr :=
  let rank (t: LMonoTy) (e: Expression.Expr) : Expression.Expr :=
    .app () (.op () (adtRankFuncName (adtNameOf t)) (.some (.arrow t .int))) e
  let ltTy : LMonoTy := LMonoTy.arrow .int (LMonoTy.arrow .int .bool)
  LExpr.mkApp () (.op () "Int.Lt" (.some ltTy)) [rank calleeAdtTy callArg, rank callerAdtTy (.fvar () callerParam (.some callerAdtTy))]

/-- Extract termination obligations from an expression. Path conditions
    through `ite` branches are accumulated and wrapped as implications
    in the obligation expression, mirroring `collectWFObligations`. -/
private def extractTermObligations
    (body : Expression.Expr)
    (recFuncNames : List String)
    (callerParam : Expression.Ident)
    (callerAdtTy : LMonoTy)
    (funcDecreasesMap : List (String × Nat × LMonoTy))
    : List Expression.Expr :=
  go body []
where
  go (e : Expression.Expr) (implications : List (Unit × Expression.Expr))
      : List Expression.Expr :=
    match _he: e with
    | .ite _ c t f =>
      let cObs := go c implications
      let tObs := go t (((), c) :: implications)
      let notC : Expression.Expr :=
        LExpr.mkApp () (.op () "Bool.Not" (.some (LMonoTy.arrow .bool .bool))) [c]
      let fObs := go f (((), notC) :: implications)
      cObs ++ tObs ++ fObs
    | .app _ _ _ =>
      match _h : getLFuncCall e with
      | (op, args) =>
        let argObs := args.attach.flatMap fun ⟨a, _⟩ => go a implications
        let callObs := match op with
          | .op _ opName _ =>
            if opName.name ∈ recFuncNames then
              match funcDecreasesMap.find? (fun (n, _, _) => n == opName.name) with
              | some (_, calleeIdx, calleeAdtTy) =>
                match args[calleeIdx]? with
                | some callArg =>
                  let ltExpr := mkAdtRankLt callArg callerParam callerAdtTy calleeAdtTy
                  [wrapImplications implications ltExpr]
                | none => []
              | none => []
            else []
          | _ => []
        argObs ++ callObs
    | .eq _ e1 e2 => go e1 implications ++ go e2 implications
    | .abs _ _ _ body => go body implications
    | .quant _ _ _ _ trigger body =>
      go trigger implications ++ go body implications
    | _ => []
  termination_by e.sizeOf
  decreasing_by
    all_goals (try term_by_mem)
    rename_i a_in
    have h := getLFuncCall_smaller _h a a_in
    subst_vars
    simp_all

/-- Build a type substitution that specializes a polymorphic datatype's type
    variables to the concrete type arguments used at a call site.
    E.g., for `MyList` with `typeArgs = ["a"]` and concrete type `MyList int`,
    produces `[("a", int)]`. -/
private def mkTySubst (tf : @TypeFactory Unit) (concreteTy : LMonoTy) : Subst :=
  match concreteTy with
  | .tcons adtName concreteArgs =>
    if concreteArgs.isEmpty then []
    else match tf.getType adtName with
      | some dt => [dt.typeArgs.zip concreteArgs]
      | none => []
  | _ => []

/-- Generate a termination-checking procedure for a single function.
    Returns `none` if the function has no recursive calls or no valid
    decreasing parameter. The polymorphic `adtRankAxioms` are specialized
    to the function's concrete decreasing-parameter type before being
    embedded as preconditions.
    The resulting procedure should NOT have preconditions checked, since
    they will already be checked by the original program, and the generated
    axioms do not use partial functions. -/
private def mkTermCheckProc
    (func : Function)
    (recFuncNames : List String)
    (funcDecreasesMap : List (String × Nat × LMonoTy))
    (adtRankAxioms : List (String × Expression.Expr))
    (tf : @TypeFactory Unit)
    (md : Imperative.MetaData Expression)
    : Option (Decl × Nat) := do
  let decrIdx ← getDecreasesIdx func
  let inputTys := func.inputs.values
  let decrTy ← inputTys[decrIdx]?
  let decrParam ← func.inputs.keys[decrIdx]?
  let body ← func.body
  let obligations := extractTermObligations body recFuncNames decrParam decrTy
    funcDecreasesMap
  if obligations.isEmpty then none
  let stmts := obligations.mapIdx fun i ob =>
    Statement.assert s!"{func.name.name}_terminates_{i}" ob md
  -- Specialize polymorphic axioms to the concrete decreasing-parameter type
  let tySubst := mkTySubst tf decrTy
  let specializedAxioms := adtRankAxioms.map fun (name, e) =>
    (name, e.applySubst tySubst)
  some (.proc {
    header := {
      name := ⟨termProcName func.name.name, ()⟩
      typeArgs := func.typeArgs
      inputs := func.inputs
      outputs := []
      noFilter := true
    }
    spec := { preconditions :=
                 (specializedAxioms.map fun (name, e) =>
                   (name, { expr := e, attr := .Free })) ++
                 (func.preconditions.mapIdx fun i p =>
                   (s!"{func.name.name}_requires_{i}", { expr := p.expr, attr := .Free })),
               postconditions := [] }
    body := stmts
  } md, obligations.length)

/-- Add a termination-check procedure as a leaf node in the cached call graph. -/
private def addTermProcToCallGraph (name : String) : CoreTransformM Unit :=
  modify fun σ => match σ.cachedAnalyses.callGraph with
  | .some cg => { σ with cachedAnalyses := { σ.cachedAnalyses with
      callGraph := .some (cg.addLeafNode name) } }
  | .none => σ

/-- Result of generating adtRank declarations for a mutual datatype block. -/
private structure AdtRankDecls where
  funcDecls : List Decl
  axioms : List (String × Expression.Expr)
  adtNames : List String

/-- Generate adtRank function declarations and axiom expressions for all
    datatypes in the mutual block containing `adtName`. -/
private def mkAdtRankDecls
    (adtName : String) (tf : @TypeFactory Unit)
    (md : Imperative.MetaData Expression)
    : AdtRankDecls :=
  match tf.toList.find? (fun b => b.any (fun d => d.name == adtName)) with
  | none => ⟨[], [], []⟩
  | some block =>
    { funcDecls := block.map fun dt =>
        Decl.func (mkAdtRankFunc (T := CoreLParams) dt) md
      axioms := block.flatMap fun dt =>
        let axioms := mkAdtRankAxioms (T := CoreLParams) dt block ()
        axioms.mapIdx fun i ax =>
          (s!"{adtRankFuncName dt.name}_{i}", ax)
      adtNames := block.map (·.name) }

/-- Main transformation: iterate over declarations, generating adtRank axioms
    and termination-checking procedures for each `recFuncBlock`. -/
def termCheck (p : Program) : CoreTransformM (Bool × Program) := do
  match (← get).factory with
  | .none => return (false, p)
  | .some _ =>
    let (changed, newDecls) ← transformDecls p.decls TypeFactory.default {}
    return (changed, { decls := newDecls })
where
  transformDecls (decls : List Decl) (tf : @TypeFactory Unit)
      (emittedAdtRank : Std.HashSet String)
      : CoreTransformM (Bool × List Decl) := do
    match decls with
    | [] => return (false, [])
    | d :: rest =>
      match d with
      | .recFuncBlock funcs md => do
        -- Step 1: error checking
        -- Skip polymorphic functions: adtRank axioms are monomorphic, so we
        -- cannot generate them for polymorphic datatypes yet. The user-facing
        -- error is in Env.addFactoryFunc; when that restriction is lifted,
        -- this filter must be updated to handle polymorphic adtRank generation.
        for func in funcs do
          if func.typeArgs.isEmpty then
            match getDecreasesIdx func with
            | none =>
              throw (s!"recursive function '{func.name.name}' requires a 'decreases' clause or a '@[cases]' parameter for termination checking")
            | some idx =>
              match func.inputs.values[idx]? with
              | some (.tcons n _) =>
                if (tf.getType n).isNone then
                  throw (s!"recursive function '{func.name.name}': decreasing parameter type '{n}' is not a known datatype")
              | some _ =>
                throw (s!"recursive function '{func.name.name}': decreasing parameter must have a datatype type")
              | none =>
                throw (s!"recursive function '{func.name.name}': decreasing parameter index {idx} is out of range")
        -- Step 2: Build a map from function name to (decreasing param index, type).
        let funcDecreasesMap := funcs.filterMap fun func => do
          if !func.typeArgs.isEmpty then none
          let idx ← getDecreasesIdx func
          let ty ← func.inputs.values[idx]?
          pure (func.name.name, idx, ty)
        -- Step 3: Generate adtRank UF declarations and per-constructor axioms.
        -- `newAdtRank` emits UF decls only for datatypes not yet in the program.
        -- `allAdtRank` collects all axioms this block needs — each $$term proc
        -- embeds axioms as preconditions, so it needs the full set even if the
        -- UF decls were emitted by a previous block.
        -- `collectAdtRank` deduplicates internally because mutual blocks can
        -- map multiple function types to the same mutual datatype block.
        let allAdtNames := funcDecreasesMap.map (fun (_, _, ty) => adtNameOf ty)
          |>.eraseDups
        let newAdtNames := allAdtNames.filter (fun n => !emittedAdtRank.contains n)
        let collectAdtRank (adtNames : List String) : AdtRankDecls :=
          let (_, revResults) : Std.HashSet String × List AdtRankDecls :=
            adtNames.foldl (init := ({}, [])) fun (seen, acc) adtName =>
              if seen.contains adtName then (seen, acc)
              else
                let r := mkAdtRankDecls adtName tf md
                (r.adtNames.foldl (fun s n => s.insert n) seen, r :: acc)
          let results := revResults.reverse
          { funcDecls := results.flatMap (·.funcDecls)
            axioms := results.flatMap (·.axioms)
            adtNames := results.flatMap (·.adtNames) }
        let newAdtRank := collectAdtRank newAdtNames
        let emittedAdtRank := newAdtRank.adtNames.foldl (fun s n => s.insert n) emittedAdtRank
        let allAdtRank := collectAdtRank allAdtNames
        incrementStat s!"{Stats.adtRankAxiomsGenerated}" allAdtRank.axioms.length
        -- Step 4: Generate a $$term procedure per function with adtRank
        -- decrease assertions at each recursive call site.
        let recNames := funcs.map (·.name.name)
        let termDecls ← funcs.filterMapM fun func => do
          match mkTermCheckProc func recNames funcDecreasesMap allAdtRank.axioms tf md with
          | some (decl, numAsserts) => do
            incrementStat s!"{Stats.termCheckProcsGenerated}"
            incrementStat s!"{Stats.termCheckAssertsEmitted}" numAsserts
            addTermProcToCallGraph (termProcName func.name.name)
            return some decl
          | none => return none
        -- Step 5: Splice adtRank decls before the rec block, term procs after.
        let (changed, rest') ← transformDecls rest tf emittedAdtRank
        if newAdtRank.funcDecls.isEmpty && termDecls.isEmpty then
          return (changed, d :: rest')
        else
          return (true, newAdtRank.funcDecls ++ [d] ++ termDecls ++ rest')
      | .type (.data block) _md => do
        let tf' : @TypeFactory Unit := tf.push block
        let (changed, rest') ← transformDecls rest tf' emittedAdtRank
        return (changed, d :: rest')
      | .func _ _ | .proc _ _ | .ax _ _ | .distinct _ _ _
      | .type (.con _) _ | .type (.syn _) _ => do
        let (changed, rest') ← transformDecls rest tf emittedAdtRank
        return (changed, d :: rest')

end TermCheck

/-- TermCheck pipeline phase: generates termination-checking procedures for
    recursive functions. Model-preserving because it only adds new
    assertions and procedures. -/
def termCheckPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "TermCheck" fun prog => do
    TermCheck.termCheck prog

end Core

end -- public section
