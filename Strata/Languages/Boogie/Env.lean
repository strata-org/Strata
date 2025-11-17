/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Program
import Strata.DL.Imperative.EvalContext

namespace Boogie
open Std (ToFormat Format format)
open Imperative

instance : ToFormat ExpressionMetadata :=
  show ToFormat Unit from inferInstance

-- ToFormat instance for Expression.Expr
instance : ToFormat Expression.Expr := by
  show ToFormat (Lambda.LExpr BoogieLParams.mono)
  infer_instance

-- Custom ToFormat instance for our specific Scope type to get the desired formatting
private def formatScope (m : Map BoogieIdent (Option Lambda.LMonoTy × Expression.Expr)) : Std.Format :=
  match m with
  | [] => ""
  | [(k, (ty, v))] => go k ty v
  | (k, (ty, v)) :: rest =>
    go k ty v ++ Format.line ++ formatScope rest
  where go k ty v :=
    match ty with
    | some ty => f!"({k} : {ty}) → {v}"
    | none => f!"{k} → {v}"

instance : ToFormat (Map BoogieIdent (Option Lambda.LMonoTy × Expression.Expr)) where
  format := formatScope

instance : Inhabited ExpressionMetadata :=
  show Inhabited Unit from inferInstance

instance : Lambda.Traceable Lambda.LExpr.EvalProvenance ExpressionMetadata where
  combine _ := ()

instance : Inhabited (Lambda.LExpr ⟨⟨ExpressionMetadata, BoogieIdent⟩, LMonoTy⟩) :=
  show Inhabited (Lambda.LExpr ⟨⟨Unit, BoogieIdent⟩, LMonoTy⟩) from inferInstance

---------------------------------------------------------------------

def PathCondition.format (p : PathCondition Expression) : Format :=
  match p with
  | [] => ""
  | [(k, v)] => f!"({k}, {v.eraseTypes})"
  | (k, v) :: rest =>
    (f!"({k}, {v.eraseTypes}){Format.line}") ++ ListMap.format' rest

def PathConditions.format (ps : PathConditions Expression) : Format :=
  match ps with
  | [] => f!""
  | p :: prest =>
    f!"{PathCondition.format p}{Format.line}" ++ PathConditions.format prest

def PathCondition.getVars (p : PathCondition Expression)
    : List (Lambda.IdentT Lambda.LMonoTy Visibility) :=
  p.map (fun (_, e) => Lambda.LExpr.freeVars e) |> .flatten |> .eraseDups

def PathConditions.getVars (ps : PathConditions Expression)
    : List (Lambda.IdentT Lambda.LMonoTy Visibility) :=
  ps.map (fun p => PathCondition.getVars p) |> .flatten |> .eraseDups

def ProofObligation.getVars (d : ProofObligation Expression)
    : List (Lambda.IdentT Lambda.LMonoTy Visibility) :=
  let o_vars := Lambda.LExpr.freeVars d.obligation
  let pc_vars := PathConditions.getVars d.assumptions
  (o_vars ++ pc_vars).eraseDups

def ProofObligation.eraseTypes (d : ProofObligation Expression) : ProofObligation Expression :=
  { label := d.label,
    assumptions := d.assumptions.map (fun m => (m.map (fun (label, expr) => (label, expr.eraseTypes)))),
    obligation := d.obligation.eraseTypes,
    metadata := d.metadata
    }

def ProofObligations.eraseTypes (ds : ProofObligations Expression) : ProofObligations Expression :=
  ds.map ProofObligation.eraseTypes

instance : ToFormat (ProofObligation Expression) where
  format o :=
    let assumptions := PathConditions.format o.assumptions
    f!"Label: {o.label}{Format.line}\
       Assumptions:{Format.line}{assumptions}\
       Proof Obligation:{Format.line}{format o.obligation}{Format.line}"

instance : ToFormat (ProofObligations Expression) where
  format os := Std.Format.joinSep (Array.map format os).toList Format.line

-- (FIXME) Parameterize by EvalContext typeclass.
def ProofObligation.create
  (label : String) (assumptions : PathConditions Expression)
  (obligation : Procedure.Check) (md : MetaData Expression := #[]):
  Option (ProofObligation Expression) :=
  open Lambda.LExpr.SyntaxMono in
  if obligation.attr == .Free then
    dbg_trace f!"{Format.line}Obligation {label} is free!{Format.line}"
    none
  --else if obligation.expr.isTrue then
  --  dbg_trace f!"{Format.line}Obligation {label} proved via evaluation!{Format.line}"
  --  none
  else
    some (ProofObligation.mk label assumptions obligation.expr md)

def ProofObligations.create
  (assumptions : PathConditions Expression)
  (obligations : ListMap String Procedure.Check) (md : MetaData Expression := #[])
  : ProofObligations Expression :=
  match obligations with
  | [] => #[]
  | o :: orest =>
    let orest' := ProofObligations.create assumptions orest md
    let o' :=
      match (ProofObligation.create o.fst assumptions o.snd md) with
      | none => #[]
      | some o' => #[o']
    o' ++ orest'

/--
A substitution map from variable identifiers to expressions.
-/
abbrev SubstMap := Map Expression.Ident Expression.Expr

structure Env where
  error : Option (Imperative.EvalError Expression)
  program : Program
  substMap : SubstMap
  exprEnv : Expression.EvalEnv
  distinct : List (List Expression.Expr)
  pathConditions : Imperative.PathConditions Expression
  warnings : List (Imperative.EvalWarning Expression)
  deferred : Imperative.ProofObligations Expression

def Env.init (empty_factory:=false): Env :=
  let σ := Lambda.LState.init
  let σ := if empty_factory then σ else σ.setFactory Boogie.Factory
  { error := none,
    program := Program.init,
    substMap := [],
    exprEnv := σ,
    distinct := [],
    pathConditions := [],
    warnings := []
    deferred := ∅ }

instance : EmptyCollection Env where
  emptyCollection := Env.init (empty_factory := true)

instance : Inhabited Env where
  default := Env.init

instance : ToFormat Env where
  format s :=
    let { error, program := _, substMap, exprEnv, distinct := _, pathConditions, warnings, deferred }  := s
    format f!"Error:{Format.line}{error}{Format.line}\
              Subst Map:{Format.line}{substMap}{Format.line}\
              Expression Env:{Format.line}{exprEnv}{Format.line}\
              Path Conditions:{Format.line}{PathConditions.format pathConditions}{Format.line}{Format.line}\
              Warnings:{Format.line}{warnings}{Format.line}\
              Deferred Proof Obligations:{Format.line}{deferred}{Format.line}"

/--
Create a substitution map from all non-global variables to their values.
-/
def oldLocalVarSubst (E : Env) : SubstMap :=
  let m := (E.exprEnv.state.dropOldest).toSingleMap
  m.map (fun (i, _, e) => (i, e))

/--
Append `subst` map to a non-global substitution map.
-/
def oldVarSubst (subst :  SubstMap) (E : Env) : SubstMap :=
  subst ++ oldLocalVarSubst E

def Env.exprEval (E : Env) (e : Expression.Expr) : Expression.Expr :=
  e.eval E.exprEnv.config.fuel E.exprEnv

def Env.pushScope (E : Env) (scope : (Lambda.Scope BoogieLParams)) : Env :=
  { E with exprEnv.state := E.exprEnv.state.push scope }

def Env.pushEmptyScope (E : Env) : Env :=
  Env.pushScope E []

def Env.popScope (E : Env) : Env :=
  { E with exprEnv.state := E.exprEnv.state.pop }

def Env.factory (E : Env) : (@Lambda.Factory BoogieLParams) :=
  E.exprEnv.config.factory

def Env.addFactory (E : Env) (f : (@Lambda.Factory BoogieLParams)) : Except Format Env := do
  let exprEnv ← E.exprEnv.addFactory f
  .ok { E with exprEnv := exprEnv }

def Env.addFactoryFunc (E : Env) (func : (Lambda.LFunc BoogieLParams)) : Except Format Env := do
  let exprEnv ← E.exprEnv.addFactoryFunc func
  .ok { E with exprEnv := exprEnv }

def Env.insertInContext (xt : (Lambda.IdentT Lambda.LMonoTy Visibility)) (e : Expression.Expr) (E : Env) : Env :=
  { E with exprEnv.state := E.exprEnv.state.insert xt.ident (xt.ty?, e) }

/--
Insert each `(x, v)` in `xs` into the context.
-/
def Env.addToContext
    (xs : Map (Lambda.IdentT Lambda.LMonoTy Visibility) Expression.Expr) (E : Env)
    : Env :=
  List.foldl (fun E (x, v) => E.insertInContext x v) E xs

-- TODO: prove uniqueness, add different prefix
def Env.genSym (x : String) (c : Lambda.EvalConfig BoogieLParams) : BoogieIdent × Lambda.EvalConfig BoogieLParams :=
  let new_idx := c.gen
  let c := c.incGen
  let new_var := c.varPrefix ++ x ++ toString new_idx
  (.temp new_var, c)

def Env.genVar' (x : String) (σ : (Lambda.LState BoogieLParams)) :
    (BoogieIdent × (Lambda.LState BoogieLParams)) :=
  let (new_var, config) := Env.genSym x σ.config
  let σ : Lambda.LState BoogieLParams := { σ with config := config }
  -- let known_vars := Lambda.LState.knownVars σ
  -- if new_var ∈ known_vars then
  --   panic s!"[LState.genVar] Generated variable {Std.format new_var} is not fresh!\n\
  --            Known variables: {Std.format σ.knownVars}"
  -- else
  --   (new_var, σ)
  (new_var, σ)

def Env.genVar (x : Expression.Ident) (E : Env) : Expression.Ident × Env :=
  let ⟨name ,_⟩ := x
  let (var, σ) := Env.genVar' name E.exprEnv
  (var, { E with exprEnv := σ })

def Env.genVars (xs : List String) (σ : Lambda.LState BoogieLParams) : (List BoogieIdent × Lambda.LState BoogieLParams) :=
  match xs with
  | [] => ([], σ)
  | x :: rest =>
    let (x', σ) := Env.genVar' x σ
    let (xrest', σ) := Env.genVars rest σ
    (x' :: xrest', σ)

/--
Generate a fresh variable using the base name and pre-existing type, if any,
from `xt`.
-/
def Env.genFVar (E : Env) (xt : (Lambda.IdentT Lambda.LMonoTy Visibility)) :
  Expression.Expr × Env :=
  let (xid, E) := E.genVar xt.ident
  let xe := match xt.ty? with
            | none => .fvar () xid none
            | some xty => .fvar () xid xty
  (xe, E)

/--
Generate fresh variables using the base names and any pre-existing types from
`xs`.
-/
def Env.genFVars (E : Env) (xs : List (Lambda.IdentT Lambda.LMonoTy Visibility)) :
  List Expression.Expr × Env :=
  let rec go (acc : List Expression.Expr) (E : Env)
             (xs : List (Lambda.IdentT Lambda.LMonoTy Visibility)) :
    List Expression.Expr × Env :=
    match xs with
    | [] => (acc.reverse, E)
    | xt :: xrest =>
      let (xe, E) := E.genFVar xt
      go (xe :: acc) E xrest
  go [] E xs

/--
Insert `(xi, .fvar xi)`, for each `xi` in `xs`, in the _oldest_ scope in `ss`,
only if `xi` is the identifier of a free variable, i.e., it is not in `ss`.
-/
def Env.insertFreeVarsInOldestScope
  (xs : List (Lambda.IdentT Lambda.LMonoTy Visibility)) (E : Env) : Env :=
  let (xis, xtyei) := xs.foldl
    (fun (acc_ids, acc_pairs) x =>
      (x.fst :: acc_ids, (x.snd, .fvar () x.fst x.snd) :: acc_pairs))
    ([], [])
  let state' := Maps.addInOldest E.exprEnv.state xis xtyei
  { E with exprEnv := { E.exprEnv with state := state' }}


open Imperative Lambda in
def PathCondition.merge (cond : Expression.Expr) (pc1 pc2 : PathCondition Expression) : PathCondition Expression :=
  let pc1' := pc1.map (fun (label, e) => (label, mkImplies cond e))
  let pc2' := pc2.map (fun (label, e) => (label, mkImplies (LExpr.ite () cond (LExpr.false ()) (LExpr.true ())) e))
  pc1' ++ pc2'
  where mkImplies (ant con : Expression.Expr) : Expression.Expr :=
  LExpr.ite () ant con (LExpr.true ())

def Env.performMerge (cond : Expression.Expr) (E1 E2 : Env)
    (_h1 : E1.error.isNone) (_h2 : E2.error.isNone) : Env :=
  let ss := Lambda.Scopes.merge cond E1.exprEnv.state E2.exprEnv.state
  let exprEnv := { E1.exprEnv with state := ss }
  let pcs1 := E1.pathConditions
  let pc1 := pcs1.newest
  let pc2 := E2.pathConditions.newest
  let pc_merged := PathCondition.merge cond pc1 pc2
  let pcs := pcs1.pop
  let pcs := Maps.addInNewest pcs pc_merged
  let deferred := E1.deferred.append E2.deferred
  { E1 with exprEnv := exprEnv, pathConditions := pcs, deferred := deferred }

def Env.merge (cond : Expression.Expr) (E1 E2 : Env) : Env :=
  if h1: E1.error.isSome then
    E1
  else if h2: E2.error.isSome then
    E2
  else
    Env.performMerge cond E1 E2 (by simp_all) (by simp_all)

end Boogie

---------------------------------------------------------------------
