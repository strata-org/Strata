/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.DL.Lambda.DtRankAxioms
public import Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.PipelinePhase
/-! # Termination Checking for Recursive Functions

This transformation generates termination-checking procedures for recursive
function blocks. For each `recFuncBlock`, it:

1. Generates `D..dtRank` UF declarations and per-constructor axioms for the
   datatypes used as decreasing measures.
2. Generates a `$$term` procedure per function that asserts `dtRank` decreases
   at each recursive call site.

See `docs/TerminationChecking.md` for the full design.
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
  | dtRankAxiomsGenerated

#derive_prefixed_toString Stats "TermCheck"

/-- Suffix for generated termination-checking procedures. -/
def termSuffix : String := "$$term"

def termProcName (name : String) : String := s!"{name}{termSuffix}"

/-- Find the decreasing parameter index for a function: explicit `measure`
    field (future), or fallback to `@[cases]` (`inlineIfConstr`). -/
private def getDecreasesIdx (func : Function) : Option Nat :=
  FuncAttr.findInlineIfConstr func.attr

/-- Build the `dtRank(callArg) < dtRank(callerParam)` expression. -/
private def mkDtRankLt
    (callArg : Expression.Expr)
    (callerParam : Expression.Ident)
    (callerDtName calleeDtName : String)
    : Expression.Expr :=
  let callerRankTy : LMonoTy := LMonoTy.arrow (.tcons callerDtName []) .int
  let calleeRankTy : LMonoTy := LMonoTy.arrow (.tcons calleeDtName []) .int
  let callerRank : Expression.Expr :=
    .app () (.op () (↑(dtRankFuncName callerDtName)) (.some callerRankTy))
      (.fvar () callerParam (.some (.tcons callerDtName [])))
  let calleeRank : Expression.Expr :=
    .app () (.op () (↑(dtRankFuncName calleeDtName)) (.some calleeRankTy))
      callArg
  let ltTy : LMonoTy := LMonoTy.arrow .int (LMonoTy.arrow .int .bool)
  .app () (.app () (.op () (↑"Int.Lt") (.some ltTy)) calleeRank) callerRank

/-- Wrap an expression with implications from accumulated path conditions,
    following the same pattern as `collectWFObligations` in Preconditions. -/
private def wrapImplications
    (implications : List Expression.Expr)
    (ob : Expression.Expr)
    : Expression.Expr :=
  let impliesTy : LMonoTy := LMonoTy.arrow .bool (LMonoTy.arrow .bool .bool)
  implications.foldr (fun lhs acc =>
    .app () (.app () (.op () (↑"Bool.Implies") (.some impliesTy)) lhs) acc) ob

/-- Extract termination obligations from an expression. Path conditions
    through `ite` branches are accumulated and wrapped as implications
    in the obligation expression, mirroring `collectWFObligations`. -/
private def extractTermObligations
    (body : Expression.Expr)
    (recFuncNames : List String)
    (callerParam : Expression.Ident)
    (callerDtName : String)
    (funcDecreasesMap : List (String × Nat × String))
    : List Expression.Expr :=
  go body []
where
  go (e : Expression.Expr) (implications : List Expression.Expr)
      : List Expression.Expr :=
    match _he: e with
    | .ite _ c t f =>
      let cObs := go c implications
      let tObs := go t (c :: implications)
      let notC : Expression.Expr :=
        .app () (.op () (↑"Bool.Not") (.some (LMonoTy.arrow .bool .bool))) c
      let fObs := go f (notC :: implications)
      cObs ++ tObs ++ fObs
    | .app _ _ _ =>
      match _h : getLFuncCall e with
      | (op, args) =>
        let argObs := args.attach.flatMap fun ⟨a, _⟩ => go a implications
        let callObs := match op with
          | .op _ opName _ =>
            if opName.name ∈ recFuncNames then
              match funcDecreasesMap.find? (fun (n, _, _) => n == opName.name) with
              | some (_, calleeIdx, calleeDtName) =>
                match args[calleeIdx]? with
                | some callArg =>
                  let ltExpr := mkDtRankLt callArg callerParam callerDtName calleeDtName
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

/-- Generate a termination-checking procedure for a single function.
    Returns `none` if the function has no recursive calls or no valid
    decreasing parameter. -/
private def mkTermCheckProc
    (func : Function)
    (recFuncNames : List String)
    (funcDecreasesMap : List (String × Nat × String))
    (dtRankAxioms : List (String × Expression.Expr))
    (md : Imperative.MetaData Expression)
    : Option (Decl × Nat) := do
  let decrIdx ← getDecreasesIdx func
  let inputTys := func.inputs.values
  let decrTy ← inputTys[decrIdx]?
  let decrParam ← func.inputs.keys[decrIdx]?
  let decrDtName ← match decrTy with
    | .tcons n _ => some n
    | _ => none
  let body ← func.body
  let obligations := extractTermObligations body recFuncNames decrParam decrDtName
    funcDecreasesMap
  if obligations.isEmpty then none
  let stmts := obligations.mapIdx fun i ob =>
    Statement.assert s!"{func.name.name}_terminates_{i}" ob md
  let paramInits := func.inputs.toList.map fun (name, ty) =>
    Statement.init name (LTy.forAll [] ty) .nondet md
  some (.proc {
    header := {
      name := ⟨termProcName func.name.name, ()⟩
      typeArgs := func.typeArgs
      inputs := []
      outputs := []
      noFilter := true
    }
    spec := { modifies := [],
               preconditions := dtRankAxioms.map fun (name, e) =>
                 (name, { expr := e, attr := .Free }),
               postconditions := [] }
    body := paramInits ++ stmts
  } md, obligations.length)

/-- Add a termination-check procedure as a leaf node in the cached call graph. -/
private def addTermProcToCallGraph (name : String) : CoreTransformM Unit :=
  modify fun σ => match σ.cachedAnalyses.callGraph with
  | .some cg => { σ with cachedAnalyses := { σ.cachedAnalyses with
      callGraph := .some (cg.addLeafNode name) } }
  | .none => σ

/-- Generate dtRank function declarations and axiom expressions for all
    datatypes in the mutual block containing `dtName`. Returns the func
    decls (to emit as top-level declarations), the named axiom expressions
    (to embed as preconditions in `$$term` procedures), and the list of
    all datatype names in the block (for deduplication tracking). -/
private def mkDtRankDecls
    (dtName : String) (tf : @TypeFactory Unit)
    (md : Imperative.MetaData Expression)
    : List Decl × List (String × Expression.Expr) × List String :=
  match tf.toList.find? (fun b => b.any (fun d => d.name == dtName)) with
  | none => ([], [], [])
  | some block =>
    let funcDecls := block.map fun dt =>
      Decl.func (mkDtRankFunc (T := CoreLParams) dt) md
    let axiomExprs := block.flatMap fun dt =>
      let axioms := mkDtRankAxioms (T := CoreLParams) dt block ()
      axioms.mapIdx fun i ax =>
        (s!"{dtRankFuncName dt.name}_{i}", ax)
    let names := block.map (·.name)
    (funcDecls, axiomExprs, names)

/-- Main transformation: iterate over declarations, generating dtRank axioms
    and termination-checking procedures for each `recFuncBlock`.

    Runs after PrecondElim in the pipeline. This avoids redundant destructor
    safety checks in `$$term` procedures: PrecondElim would insert them for
    partial function calls in the `$$term` body (e.g., `IntList..tl(xs)`),
    but those are already proved in the original function's body WF procedure.
    Running after PrecondElim means the `$$term` procedures are never seen by
    PrecondElim. Termination proofs never require function preconditions —
    they only assert `dtRank(callArg) < dtRank(callerParam)`. -/
def termCheck (p : Program) : CoreTransformM (Bool × Program) := do
  match (← get).factory with
  | .none => return (false, p)
  | .some _ =>
    let (changed, newDecls) ← transformDecls p.decls TypeFactory.default {}
    return (changed, { decls := newDecls })
where
  transformDecls (decls : List Decl) (tf : @TypeFactory Unit)
      (emittedDtRank : Std.HashSet String)
      : CoreTransformM (Bool × List Decl) := do
    match decls with
    | [] => return (false, [])
    | d :: rest =>
      match d with
      | .recFuncBlock funcs md => do
        -- Skip polymorphic functions: dtRank axioms are monomorphic, so we
        -- cannot generate them for polymorphic datatypes yet. The user-facing
        -- error is in Env.addFactoryFunc; when that restriction is lifted,
        -- this filter must be updated to handle polymorphic dtRank generation.
        let funcDecreasesMap := funcs.filterMap fun func => do
          if !func.typeArgs.isEmpty then none
          let idx ← getDecreasesIdx func
          let ty ← func.inputs.values[idx]?
          let dtName ← match ty with
            | .tcons n _ => some n
            | _ => none
          pure (func.name.name, idx, dtName)
        let allDtNames := funcDecreasesMap.map (·.2.2) |>.eraseDups
        let newDtNames := allDtNames.filter (fun n => !emittedDtRank.contains n)
        let (dtRankFuncDecls, _, emittedBlockNames) :=
          newDtNames.foldl (init := ([], [], [])) fun (decls, axioms, names) dtName =>
            if names.contains dtName then (decls, axioms, names)
            else
              let (newDecls, newAxioms, blockNames) := mkDtRankDecls dtName tf md
              (decls ++ newDecls, axioms ++ newAxioms, names ++ blockNames)
        let emittedDtRank := emittedBlockNames.foldl (fun s n => s.insert n) emittedDtRank
        let (_, dtRankAxioms, _) :=
          allDtNames.foldl (init := ([], [], [])) fun (decls, axioms, names) dtName =>
            if names.contains dtName then (decls, axioms, names)
            else
              let (newDecls, newAxioms, blockNames) := mkDtRankDecls dtName tf md
              (decls ++ newDecls, axioms ++ newAxioms, names ++ blockNames)
        incrementStat s!"{Stats.dtRankAxiomsGenerated}" dtRankAxioms.length
        let recNames := funcs.map (·.name.name)
        let termDecls ← funcs.filterMapM fun func => do
          match mkTermCheckProc func recNames funcDecreasesMap dtRankAxioms md with
          | some (decl, numAsserts) => do
            incrementStat s!"{Stats.termCheckProcsGenerated}"
            incrementStat s!"{Stats.termCheckAssertsEmitted}" numAsserts
            addTermProcToCallGraph (termProcName func.name.name)
            return some decl
          | none => return none
        let (changed, rest') ← transformDecls rest tf emittedDtRank
        if dtRankFuncDecls.isEmpty && termDecls.isEmpty then
          return (changed, d :: rest')
        else
          return (true, dtRankFuncDecls ++ [d] ++ termDecls ++ rest')
      | .func _func _md => do
        let (changed, rest') ← transformDecls rest tf emittedDtRank
        return (changed, d :: rest')
      | .type (.data block) _md => do
        let tf' : @TypeFactory Unit := tf.push block
        let (changed, rest') ← transformDecls rest tf' emittedDtRank
        return (changed, d :: rest')
      | _ => do
        let (changed, rest') ← transformDecls rest tf emittedDtRank
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
