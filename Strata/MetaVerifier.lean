/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Meta
import Lean.Elab.Tactic

import Strata.Languages.Core.Verifier
import Strata.Transform.LoopElim
public import Strata.Languages.C_Simp.Verify
public import Strata.Languages.Boole.Verify
import Strata.DL.Imperative.SMTUtils
public import Strata.DL.SMT.Denote
public import Strata.DL.SMT.Translate

open Lean hiding Options

public section

namespace Strata.SMT

structure SanitizedContext where
  sorts : Array Core.SMT.Sort := #[]
  ufs : Array UF := #[]
  ifs : Array Core.SMT.IF := #[]
  axms : Array Term := #[]
  tySubst : Map String TermType := []
deriving Repr, Inhabited, DecidableEq

def SanitizedContext.ofCore (ctx : Core.SMT.Context) : SanitizedContext :=
  { sorts := ctx.sorts, ufs := ctx.ufs, ifs := ctx.ifs, axms := ctx.axms, tySubst := ctx.tySubst }

def SanitizedContext.toCore (ctx : SanitizedContext) : Core.SMT.Context :=
  { sorts := ctx.sorts
    ufs := ctx.ufs
    ifs := ctx.ifs
    axms := ctx.axms
    tySubst := ctx.tySubst
    typeFactory := #[]
    seenDatatypes := {}
    datatypeFuns := Map.empty }

abbrev SMTVC := String × SanitizedContext × List Term × Term
abbrev SMTVCs := List SMTVC

end Strata.SMT

namespace Core

abbrev CoreVC := Env × Imperative.ProofObligation Expression
abbrev coreVCs := List (Env × Imperative.ProofObligation Expression)

def genVCsSingleENV (E : Env) : Option coreVCs := do
  match E.error with
  | some _ => none
  | _ => return E.deferred.toList.map (fun ob => (E, ob))

def genVCs (program : Program) (options : VerifyOptions := .default) : Option coreVCs := do
  let program := (loopElim program).fst
  match Core.typeCheckAndEval options program with
  | .error _ => none
  | .ok (pEs, _stats) =>
    let VCss ← List.mapM (fun pE => genVCsSingleENV pE) pEs
    return VCss.flatten.reverse

end Core

namespace C_Simp

def genVCs (program : Strata.C_Simp.Program) (options : Core.VerifyOptions := .default) : Option Core.coreVCs := do
  let program := Strata.to_core program
  Core.genVCs program options

end C_Simp

namespace Boole

def genVCs (program : Strata.Boole.Program) (gctx : Strata.GlobalContext) (options : Core.VerifyOptions := .default) : Option Core.coreVCs := do
  let program ← (Strata.Boole.toCoreProgram program gctx).toOption
  Core.genVCs program options

end Boole

namespace Strata

/--
Generate verification conditions for a `Strata.Program` by translating it to the
appropriate frontend verifier and collecting its deferred proof obligations.
-/
def genCoreVCs (program : Program) : Option Core.coreVCs := do
  if program.dialect == "Core" then
    let (program, #[]) := TransM.run default (translateProgram program) | none
    Core.genVCs program { (default : Core.VerifyOptions) with verbose := .quiet : Core.VerifyOptions }
  else if program.dialect == "C_Simp" then
    let (program, #[]) := C_Simp.TransM.run default (C_Simp.translateProgram program.commands) | none
    C_Simp.genVCs program { (default : Core.VerifyOptions) with verbose := .quiet : Core.VerifyOptions }
  else if program.dialect == "Boole" then
    match Boole.getProgram program with
    | .ok booleProgram =>
      Boole.genVCs booleProgram program.globalContext { (default : Core.VerifyOptions) with verbose := .quiet : Core.VerifyOptions }
    | .error _ => none
  else
    none

/--
Remove solver-side caches that destabilize definitional equality in metaprograms.

At the moment this is semantically harmless for denotation because
`Strata.DL.SMT.Denote.denoteQuery` rejects contexts with datatype machinery
(`typeFactory`, `seenDatatypes`, `datatypeFuns`) populated anyway.
-/
private def sanitizeSMTContext (ctx : Core.SMT.Context) : SMT.SanitizedContext :=
  SMT.SanitizedContext.ofCore ctx

def Core.ProofObligation.toSMTObligation (E : Core.Env) (ob : Imperative.ProofObligation Core.Expression) :
  Option SMT.SMTVC := do
    let maybeTerms := Core.ProofObligation.toSMTTerms E ob
    match maybeTerms with
    | .error _ => none
    | .ok (ts, t, ctx, _stats) =>
      (ob.label, sanitizeSMTContext ctx, ts, t)

/--
Interpret a list of SMT verification conditions as the conjunction of their
denotations.
-/
noncomputable def denoteQueries (vcs : SMT.SMTVCs) : Option Prop := do
  match vcs with
  | [] => return True
  | (_, ctx, ts, t) :: vcs =>
    let p ← denoteQuery ctx.toCore ts t
    go vcs p
where
  go vcs p : Option Prop := do
  match vcs with
  | [] => return p
  | (_, ctx, ts, t) :: vcs =>
    let q ← denoteQuery ctx.toCore ts t
    go vcs (p ∧ q)

def toSMTVCs (vcs : Core.coreVCs) : Option SMT.SMTVCs := do
  match vcs with
  | [] => return []
  | (E, ob) :: vcs =>
    let (label, ctx, ts, t) ← Core.ProofObligation.toSMTObligation E ob
    let vcs ← toSMTVCs vcs
    return (label, ctx, ts, t) :: vcs

/--
Generate SMT verification conditions for a `Strata.Program`.
-/
def genSMTVCs (program : Program) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCs program
  toSMTVCs coreVCs

/--
State semantic correctness of the SMT verification conditions generated for a
program.
-/
def smtVCsCorrect (program : Program) : Prop :=
  match genSMTVCs program with
  | some vcs => (denoteQueries vcs).getD False
  | none     => False

theorem toSMTVCs_cons :
    toSMTVCs ((E, ob) :: coreVCs) = some vcs →
    ∃ label ctx ts t smtVCs, vcs = (label, ctx, ts, t) :: smtVCs ∧
    Core.ProofObligation.toSMTObligation E ob = some (label, ctx, ts, t) ∧
    toSMTVCs coreVCs = some smtVCs := by
  simp only [toSMTVCs, Option.bind_eq_bind, Option.bind]
  grind

namespace SMT

instance {α : Type u} {β : Type v} [hu : ToLevel.{u}] [hv : ToLevel.{v}] [ToExpr α] [ToExpr β] : ToExpr (Map α β) where
  toExpr m   := mkApp3 (.const ``Map.ofList [toLevel.{u}, toLevel.{v}]) (toTypeExpr α) (toTypeExpr β)
                       (@toExpr _ (@instToExprListOfToLevel _ ToLevel.max.{u, v} _) m.toList)
  toTypeExpr := mkApp2 (.const ``Map [toLevel.{u}, toLevel.{v}]) (toTypeExpr α) (toTypeExpr β)

deriving instance ToExpr for TermPrimType
deriving instance ToExpr for TermType
deriving instance ToExpr for TermVar
deriving instance ToExpr for UF
deriving instance ToExpr for TermPrim
deriving instance ToExpr for Op.Core
deriving instance ToExpr for Op.Num
deriving instance ToExpr for Op.BV
deriving instance ToExpr for Op.Strings
deriving instance ToExpr for Op.DatatypeFuncs
deriving instance ToExpr for Op.Arrays
deriving instance ToExpr for Op
deriving instance ToExpr for QuantifierKind
deriving instance ToExpr for SMT.Term
deriving instance ToExpr for Core.SMT.Sort
deriving instance ToExpr for Core.SMT.IF
deriving instance ToExpr for SanitizedContext
meta instance : ToExpr Strata.Uri where
  toTypeExpr := mkConst ``Strata.Uri
  toExpr
    | .file p => mkApp (mkConst ``Strata.Uri.file) (toExpr p)

meta instance : ToExpr ExprSourceLoc where
  toTypeExpr := mkConst ``ExprSourceLoc
  toExpr e := mkApp2 (mkConst ``ExprSourceLoc.mk) (toExpr e.uri) (toExpr e.range)
deriving instance ToExpr for Lambda.LMonoTy

instance [ToExpr α] : ToExpr (Lambda.Identifier α) where
  toExpr id :=
    mkApp3 (.const ``Lambda.Identifier.mk []) (toTypeExpr α)
      (toExpr id.name)
      (toExpr id.metadata)
  toTypeExpr := mkApp2 (.const ``Lambda.Identifier []) (toTypeExpr String) (toTypeExpr α)

instance [ToExpr α] : ToExpr (Lambda.LConstr α) where
  toExpr c :=
    mkApp4 (.const ``Lambda.LConstr.mk []) (toTypeExpr α)
      (toExpr c.name)
      (toExpr c.args)
      (toExpr c.testerName)
  toTypeExpr := .app (.const ``Lambda.LConstr []) (toTypeExpr α)

instance [ToExpr α] : ToExpr (Lambda.LDatatype α) where
  toExpr dt :=
    mkApp5 (.const ``Lambda.LDatatype.mk []) (toTypeExpr α)
      (toExpr dt.name)
      (toExpr dt.typeArgs)
      (toExpr dt.constrs)
      (mkApp2 (.const ``Eq.refl [1]) (toTypeExpr Bool) (toExpr true))
  toTypeExpr := .app (.const ``Lambda.LDatatype []) (toTypeExpr α)

def _root_.Lambda.TypeFactory.ofList (dts : List (Lambda.MutualDatatype IDMeta))
  : @Lambda.TypeFactory IDMeta :=
  dts.foldl (fun tf dt => (tf.addMutualBlock dt).toOption.get!) Lambda.TypeFactory.default

instance [ToExpr α] : ToExpr (@Lambda.TypeFactory α) where
  toExpr tf := mkApp2 (.const ``Lambda.TypeFactory.ofList []) (toTypeExpr α) (toExpr tf.toList)
  toTypeExpr := .app (.const ``Lambda.TypeFactory []) (toTypeExpr α)

instance : ToExpr (Std.HashSet String) where
  toExpr s := mkApp4 (.const ``Std.HashSet.ofList [0]) (toTypeExpr String)
                     (mkApp2 (.const ``instBEqOfDecidableEq [0]) (toTypeExpr String) (.const ``instDecidableEqString []))
                     (.const ``instHashableString []) (toExpr s.toList)
  toTypeExpr := .app (.const ``Std.HashSet []) (toTypeExpr String)

def createGoal : SMTVC → MetaM MVarId := fun (label, ctx, ts, t) => do
  match translateQuery ctx.toCore ts t with
  | .error e =>
    logInfo m!"Error translating query"
    throwError e
  | .ok e =>
    trace[debug] "e := {e}"
    Meta.check e
    let .mvar mv ← Meta.mkFreshExprMVar e (userName := Translate.symbolToName label)
      | throwError "Failed to create goal"
    return mv

end SMT

end Strata

end -- public section

namespace Strata

public section

namespace Meta

def andN (ps : List Lean.Expr) : Lean.Expr :=
  match ps with
  | [] => .const ``True []
  | p :: ps => go ps p
where
  go ps P : Lean.Expr :=
  match ps with
  | [] => P
  | p :: ps => go ps (mkApp2 (.const ``And []) P p)

def andNIntro (hps : List (Lean.Expr × Lean.Expr)) : Lean.Expr :=
  match hps with
  | [] => .const ``True.intro []
  | (p, hp) :: ps => go ps p hp
where
  go ps P hP : Lean.Expr :=
  match ps with
  | [] => hP
  | (p, hp) :: ps => go ps (mkApp2 (.const ``And []) P p) (mkApp4 (.const ``And.intro []) P p hP hp)

def nativeDecide (p : Lean.Expr) : MetaM Lean.Expr := do
  let hp ← Meta.synthInstance (.app (.const ``Decidable []) p)
  let auxDeclName ← mkNativeAuxDecl `_genSMTVCs (.const ``Bool []) (mkApp2 (.const ``decide []) p hp)
  let b := .const auxDeclName []
  return mkApp3 (.const ``of_decide_eq_true []) p hp
                (mkApp3 (.const ``Lean.ofReduceBool []) b (.const ``true [])
                        (mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``true [])))
where
  mkNativeAuxDecl (baseName : Name) (type value : Lean.Expr) : MetaM Name := do
    let auxName ← Lean.mkAuxDeclName baseName
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

private unsafe def genSMTVCsUnsafe (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  let some program := type.app1? ``Strata.smtVCsCorrect | throwError "Expected a Strata.smtVCsCorrect goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrect
  let ovcs := .app (.const ``Strata.genSMTVCs []) program
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  trace[debug] m!"Generated {repr evcs}"
  let rhs := toExpr (some evcs)
  let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs rhs
  let hEQVCs ← nativeDecide eqVCs
  let r ← mv.rewrite (← mv.getType) hEQVCs
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  let mvs ← evcs.mapM SMT.createGoal
  trace[debug] m!"Created {mvs.length} SMT VC goals: {mvs}"
  let ps ← mvs.mapM MVarId.getType
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign hP
  return mvs

@[implemented_by genSMTVCsUnsafe]
meta opaque genSMTVCs (mv : MVarId) : MetaM (List MVarId)

end Meta

end -- public section

public section

namespace Tactic

/--
Generate one Lean goal per SMT verification condition in a goal of the form
`Strata.smtVCsCorrect program`.
-/
syntax (name := genSMTVCs) "gen_smt_vcs" : tactic

open Lean Elab Tactic in
@[tactic genSMTVCs] meta def evalGenSMTVCs : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_smt_vcs) =>
    let mvs ← Meta.genSMTVCs (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

end Tactic

end -- public section

end Strata
