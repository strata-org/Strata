/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Util.Props
import Strata.Languages.Boogie.Names

namespace Boogie
namespace CallElim

abbrev Stmt := Imperative.Stmt Boogie.Expression Boogie.Command

protected def ident2havoc (ident : Boogie.Expression.Ident)
  : Stmt := Statement.havoc ident

protected def idents2havocs (ident : List Boogie.Expression.Ident)
  : List Stmt := ident.map CallElim.ident2havoc

protected def ident2expr (ident : Boogie.Expression.Ident)
  : Boogie.Expression.Expr
  := Lambda.LExpr.fvar ident none

protected def idents2exprs (ident : List Boogie.Expression.Ident)
  : List Boogie.Expression.Expr
  := ident.map CallElim.ident2expr

abbrev VarMap := Map Boogie.Expression.Ident Boogie.Expression.Ident

structure CallElimConfig where
  -- program : Boogie.Program := .init
  counter : Nat := 0
  exprMap : VarMap := []

abbrev CallElimM := StateM CallElimConfig

-- returns the old counter value
def getCounter : CallElimM Nat := do
  return (← get).counter

-- returns the old counter value, and increment it
def genCounter : CallElimM Nat := do
  modifyGet f where f σ := (σ.counter, { σ with counter := σ.counter + 1 })

def mapExpr (ident: Boogie.Expression.Ident)
  : CallElimM (Option Boogie.Expression.Ident) := do
    return (← get).exprMap.find? ident

def addToExprMap (fr : Boogie.Expression.Ident) (to: Boogie.Expression.Ident)
  : CallElimM Unit := do
    modify f where f σ := { σ with exprMap := σ.exprMap ++ [(fr, to)] }

def resetExprMap : CallElimM Unit := do
    modify f where f σ := { σ with exprMap := [] }

----

/--
ad-hoc method to eliminate option.
TODO: implement a version requiring a proof
-/
def get! {α : Type u} [Inhabited α] (o : Option α) : α :=
  match o with
  | none => panic! s!"get! is called on a none value of type"
  | some o' => o'

def getDecl? (p : Program) (ident : Boogie.Expression.Ident)
  : CallElimM (Option Boogie.Decl) :=
  return p.find? .var ident

-- TODO: replace this with a version requiring proof of isSome = true
def getDecl! (p : Program) (ident : Boogie.Expression.Ident)
  : CallElimM (Boogie.Decl)
  := do return (← getDecl? p ident).get!

def getTy? (p : Program) (ident : Boogie.Expression.Ident)
  : CallElimM (Option Boogie.Expression.Ty) := do
  return p.getTy? ident

def getTy! (p : Program) (ident : Boogie.Expression.Ident)
  : CallElimM (Boogie.Expression.Ty)
  := do return (← getTy? p ident).get!

/-
Retrieves a fresh identifier for the given identifier "ident" within old(...)
-/
def genOldExprIdent (ident : Boogie.Expression.Ident)
  : CallElimM Boogie.Expression.Ident := do
    match (← mapExpr ident) with
    | some targetIdent => return targetIdent
    | none =>
      let to := .temp $ "old_" ++ ident.2 ++ "_" ++ toString (← genCounter)
      -- TODO: name clash possible. Use @ or something else when the parser is fixed. Extract this Names.lean
      addToExprMap ident to
      return to

def genOldExprIdents (idents : List Boogie.Expression.Ident)
  : CallElimM (List Boogie.Expression.Ident)
  := idents.mapM genOldExprIdent

-- TODO: Should check if the variable is locally defined. If so, return false, because it shadows the global variable?
-- Or maybe we can have the old expression always refer to the global variable even if it is shadowed.
-- Shouldn't be hard to change
def isGlobalVar (p : Boogie.Program) (ident : Boogie.Expression.Ident) : CallElimM Bool :=
  return (p.getVar? ident).isSome

/--
Generate init/assign statements to be inserted prior to call-site.
Probably only useful for call-elimination pass
-/
def createOldVarInits
  (vars : List Boogie.Expression.Ident)
  (pairs : List (Boogie.Expression.Ident × Boogie.Expression.Ty))
  : List Boogie.Statement :=
  let inits : (List Boogie.Statement) :=
    (pairs.zip vars).map (λ p ↦ .init p.fst.fst p.fst.snd (Lambda.LExpr.fvar p.snd none))
  inits

/--
returned list has the shape
(generated_name, ty)
-/
def genOldExprIdentsPair (p : Program) (idents : List Boogie.Expression.Ident)
  : CallElimM (List (Boogie.Expression.Ident × Boogie.Expression.Ty)) := do
  let gen_idents ← (genOldExprIdents idents)
  let tys ← idents.mapM (getTy! p)
  return gen_idents.zip tys

-- Note: if the variable has already been evaluated, then substitute the old variable to that value, otherwise substitute with the variable
def createOldVarsSubst
  (vars : List Boogie.Expression.Ident)
  (pairs : List (Boogie.Expression.Ident × Boogie.Expression.Ty)):
  Map Boogie.Expression.Ident Boogie.Expression.Expr :=
  let exprs : List Expression.Expr :=
      pairs.map (fun p => (.fvar p.fst none))
  List.zip vars exprs

-- TODO: Decompose the individual functions into proof-carrying functions
def callElimStmt (st: Boogie.Statement) (p : Boogie.Program) (wf : WF.WFStatementProp p st)
  : CallElimM (List Boogie.Statement) := do
    match st with
      | .call lhs procName args =>
        -- we have a call statement
        -- ASSUME: procName is a declared procedure (can probably be produced by the type checker)
        -- ASSUME: args are defined variables in the program (can probably be produced by the type checker)
        -- ASSUME: lhs are not already declared (can probably be produced by the type checker)
        -- generate versions of the old variables
        -- start out by resetting the varMap for old expressions, because this is a new call
        resetExprMap
        let proc := Boogie.Program.Procedure.find p procName wf.defined
        -- TODO: get the witness from WFProg
        let postconditions := Boogie.OldExpressions.normalizeOldChecks proc.spec.postconditions
        -- extract old variables in all post conditions
        let oldVars := postconditions.values.map Boogie.Procedure.Check.expr
                      |> List.map Boogie.OldExpressions.normalizeOldExpr
                      |> List.foldl (λ s x ↦ s ++ Boogie.OldExpressions.extractOldExprVars x) []

        -- filter out non-global variables
        let oldVars ← oldVars.filterM (isGlobalVar p)
        -- ASSERT: oldVars do not clash with existing global variables
        let oldVars := List.eraseDups oldVars
        -- ASSERT: oldVars has no duplicates

        -- Monadic operation, generate var mapping for each unique oldVars.
        let pairs : List (Boogie.Expression.Ident × Boogie.Expression.Ty) ← genOldExprIdentsPair p oldVars
        -- ASSERT: each generated identifier is unique with respect to each other and those global variables

        -- initialize/declare the newly generated variables
        let old_init := createOldVarInits oldVars pairs

        -- construct substitutions of old variables
        let old_subst := createOldVarsSubst oldVars pairs

        -- only need to substitute post conditions.
        let postconditions := OldExpressions.substsOldInProcChecks old_subst postconditions
        -- ASSERT: post condition does not contain "old" expressions
        -- ASSERT: each old variable properly maps to the generated variable

        -- generate havoc for return variables, modified variables
        let havoc_ret := CallElim.idents2havocs lhs
        let havoc_mod := CallElim.idents2havocs proc.spec.modifies
        let havocs := havoc_ret ++ havoc_mod

        -- construct substitutions for argument and return
        let arg_subst : List (Boogie.Expression.Ident × Boogie.Expression.Expr)
                      := (proc.header.inputs.map Prod.fst).zip args
        let ret_subst : List (Boogie.Expression.Ident × Boogie.Expression.Expr)
                      := (proc.header.outputs.map Prod.fst).zip $ CallElim.idents2exprs lhs

        -- construct assumes and asserts in place of pre/post conditions
        let (assumes, asserts) : List Stmt × List Stmt :=
              -- generate asserts based on pre-conditions, substituting procedure arguments
              let pres := proc.spec.preconditions.values.map Boogie.Procedure.Check.expr
                |> List.map (λ pred ↦ Lambda.LExpr.substFvars pred arg_subst)
                |> List.map (λ pred : Boogie.Expression.Expr ↦
                  Statement.assert s!"assert: {Std.format pred}" pred)
              -- generate assumes based on post-conditions, substituting procedure arguments and returns
              let posts := postconditions.values.map Boogie.Procedure.Check.expr
                |> List.map (λ pred ↦ Lambda.LExpr.substFvars pred (arg_subst ++ ret_subst))
                |> List.map (λ pred : Boogie.Expression.Expr ↦
                  Statement.assume s!"assume: {Std.format pred}" pred)
              (pres, posts)
        return old_init ++ havocs ++ assumes ++ asserts
      | _ => return [ st ]

def callElimStmts (ss: List Boogie.Statement) (prog : Boogie.Program) (wf : WF.WFStatementsProp prog ss)
  : CallElimM (List Boogie.Statement) := do match ss with
    | [] => return []
    | s :: ss =>
      let ⟨wfs, wfss⟩ : (WF.WFStatementProp prog _) ×' _ := ListP.split wf
      let s' := (callElimStmt s prog wfs)
      let ss' := (callElimStmts ss prog wfss)
      return (← s') ++ (← ss')

-- TODO: integrate the program parameter into the state as well
-- Walk through dcls, eliminating procedure call in them
def callElimL (dcls : List Boogie.Decl) (prog : Boogie.Program) (wf : WF.WFDeclsProp prog dcls)
  : CallElimM (List Boogie.Decl) :=
  match dcls with
  | [] => return []
  | d :: ds =>
    let ⟨wfd, wfds⟩ : (WF.WFDeclProp prog _) ×' _ := ListP.split wf
    match d with
    | .proc p =>
      return Boogie.Decl.proc { p with body := ← (callElimStmts p.body prog wfd.wfstmts) } :: (← (callElimL ds prog wfds))
    | _       => return d :: (← (callElimL ds prog wfds))

-- walk through all procedure bodies
def callElim' (p : WF.WFProgram) : CallElimM Boogie.Program := return { decls := (← (callElimL p.self.decls p.self p.prop.wfdecls)) }

def callElim (p : WF.WFProgram)
  : Boogie.Program :=
  (StateT.run (callElim' p) { }).fst

end CallElim
end Boogie
