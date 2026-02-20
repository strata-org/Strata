/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean

import Strata.Languages.Core.Verifier
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Boole.VerifyOld
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser
import Strata.DL.SMT.Denote
import Strata.DL.SMT.Translate

open Lean hiding Options

namespace Strata.SMT

abbrev SMTVC := String × Core.SMT.Context × List Term × Term
abbrev SMTVCs := List SMTVC

end Strata.SMT

namespace Core

abbrev CoreVC := Env × Imperative.ProofObligation Expression
abbrev coreVCs := List (Env × Imperative.ProofObligation Expression)

def genVCsSingleENV (pE : Program × Env) : Option coreVCs := do
  let (_, E) := pE
  match E.error with
  | some _ => none
  | _ => return E.deferred.toList.map (fun ob => (E, ob))

def genVCs (program : Program) (options : Options := Options.default) : Option coreVCs := do
  match Core.typeCheckAndPartialEval options program with
  | .error _ => none
  | .ok pEs =>
    let VCss ← List.mapM (fun pE => genVCsSingleENV pE) pEs
    return VCss.flatten.reverse

end Core

namespace C_Simp

def genVCs (program : Strata.C_Simp.Program) (options : Options := Options.default) : Option Core.coreVCs := do
  let program := Strata.to_core program
  Core.genVCs program options

end C_Simp

namespace Boole

def genVCs (program : Strata.Boole.Program) (options : Options := Options.default) : Option Core.coreVCs := do
  let program := Strata.Boole.toCoreProgram program
  Core.genVCs program options

end Boole

namespace Strata

def genCoreVCs (program : Program) : Option Core.coreVCs := do
  if program.dialect == "Core" then
    let (program, #[]) := TransM.run default (translateProgram program) | none
    Core.genVCs program { (default : Options) with verbose := .quiet : Options }
  else if program.dialect == "C_Simp" then
    let (program, #[]) := C_Simp.TransM.run (C_Simp.translateProgram (program.commands)) | none
    C_Simp.genVCs program { (default : Options) with verbose := .quiet : Options }
  else if program.dialect == "Boole" then
    let (program, #[]) := Boole.TransM.run default (Boole.translateProgram program) | none
    Boole.genVCs program { (default : Options) with verbose := .quiet : Options }
  else
    none

def Core.ProofObligation.toSMTObligation (E : Core.Env) (ob : Imperative.ProofObligation Core.Expression) :
  Option SMT.SMTVC := do
    let maybeTerms := Core.ProofObligation.toSMTTerms E ob
    match maybeTerms with
    | .error _ => none
    | .ok (terms, ctx) =>
        let t :: ts := terms | none
        let (ts, t) := ((t :: ts).dropLast, (t :: ts).getLast?.get rfl)
        let t := SMT.Factory.not t
        (ob.label, ctx, ts, t)

def denoteProofObligation (E : Core.Env) (ob : Imperative.ProofObligation Core.Expression) :
  Option Prop := do
  sorry

theorem DPO_isSome_of_DQ_isSome :
    (Core.ProofObligation.toSMTObligation E ob) = some (label, ctx, ts, t) →
    (denoteQuery ctx ts t).isSome → (denoteProofObligation E ob).isSome := by
  sorry

theorem DPO_of_DQ :
    Core.ProofObligation.toSMTObligation E ob = some (label, ctx, ts, t) →
    denoteQuery ctx ts t = some p → denoteProofObligation E ob = some q →
    p → q := by
  sorry

def denoteProofObligations (vcs : Core.coreVCs) : Option Prop := do
  match vcs with
  | [] => return True
  | (E, ob) :: vcs =>
    let p ← denoteProofObligation E ob
    go vcs p
where
  go vcs p : Option Prop := do
  match vcs with
  | [] => return p
  | (E, ob) :: vcs =>
    let q ← denoteProofObligation E ob
    go vcs (p ∧ q)

def coreVCsCorrect (program : Program) : Prop :=
  match genCoreVCs program with
  | some vcs => (denoteProofObligations vcs).getD False
  | none     => False

noncomputable def denoteQueries (vcs : SMT.SMTVCs) : Option Prop := do
  match vcs with
  | [] => return True
  | (_, ctx, ts, t) :: vcs =>
    let p ← denoteQuery ctx ts t
    go vcs p
where
  go vcs p : Option Prop := do
  match vcs with
  | [] => return p
  | (_, ctx, ts, t) :: vcs =>
    let q ← denoteQuery ctx ts t
    go vcs (p ∧ q)

def toSMTVCs vcs := do
  match vcs with
  | [] => return []
  | (E, ob) :: vcs =>
    let (ctx, ts, t) ← Core.ProofObligation.toSMTObligation E ob
    let vcs ← toSMTVCs vcs
    return (ctx, ts, t) :: vcs

def genSMTVCs (program : Program) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCs program
  toSMTVCs coreVCs

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

theorem DPOsGo_isSome_of_DQsGo_isSome  :
    toSMTVCs coreVCs = some smtVCs → (denoteQueries.go smtVCs p).isSome →
    (denoteProofObligations.go coreVCs q).isSome := by
  intro h hs
  induction coreVCs generalizing smtVCs p q with
  | nil => rfl
  | cons coreVC coreVCs ih =>
    let (E, ob) := coreVC
    let ⟨_, ctx, ts, t, smtVCs, hctx, hob, hrest⟩ := toSMTVCs_cons h
    simp only [hctx, Option.bind, denoteQueries.go, Option.bind_eq_bind] at hs
    match hp' : denoteQuery ctx ts t with
    | none => grind
    | some p' =>
      simp only [hp'] at hs
      simp only [denoteProofObligations.go, Option.bind_eq_bind, Option.bind]
      split
      · have := DPO_isSome_of_DQ_isSome hob (Option.isSome_of_eq_some hp')
        simp_all
      · simp [ih hrest hs]

theorem DPOs_isSome_of_DQs_isSome  :
    toSMTVCs coreVCs = some smtVCs → (denoteQueries smtVCs).isSome →
    (denoteProofObligations coreVCs).isSome := by
  intro h hs
  match coreVCs with
  | [] => rfl
  | (E, ob) :: coreVCs =>
    have ⟨_, ctx, ts, t, smtVCs, hctx, hob, hrest⟩ := toSMTVCs_cons h
    simp only [denoteQueries, hctx, Option.bind_eq_bind, Option.bind] at hs
    match hp : denoteQuery ctx ts t with
    | none => grind
    | some p =>
      simp only [hp] at hs
      simp only [denoteProofObligations, Option.bind_eq_bind, Option.bind]
      split
      · have := DPO_isSome_of_DQ_isSome hob (Option.isSome_of_eq_some hp)
        simp_all
      · simp [DPOsGo_isSome_of_DQsGo_isSome hrest hs]

theorem DPOsGo_of_DQsGo  :
    toSMTVCs coreVCs = some smtVCs →
    denoteQueries.go smtVCs p = some P →
    denoteProofObligations.go coreVCs q = some Q →
    (p → q) → P → Q := by
  intro h
  induction coreVCs generalizing smtVCs p q P Q with
  | nil => simp_all [denoteProofObligations.go, denoteQueries.go, toSMTVCs]
  | cons coreVC coreVCs ih =>
    let (E, ob) := coreVC
    let ⟨_, ctx, ts, t, smtVCs, hctx, hob, hrest⟩ := toSMTVCs_cons h
    simp only [hctx] at h ⊢
    simp only [denoteQueries.go, Option.bind_eq_bind, denoteProofObligations.go]
    match hp' : denoteQuery ctx ts t with
    | none => simp_all
    | some p' =>
      match hq' : denoteProofObligation E ob with
      | none => simp_all
      | some q' =>
        simp only [Option.bind_some]
        intro hp hq hpq
        have hp'q' := DPO_of_DQ hob hp' hq'
        have hpp'qq' : p ∧ p' → q ∧ q' := fun ⟨hp, hp'⟩ => And.intro (hpq hp) (hp'q' hp')
        apply ih hrest hp hq hpp'qq'

theorem DPOs_of_DQs  :
    toSMTVCs coreVCs = some smtVCs →
    denoteQueries smtVCs = some P →
    denoteProofObligations coreVCs = some Q →
    P → Q := by
  intro h
  match coreVCs with
  | [] => simp_all [denoteProofObligations, denoteQueries, toSMTVCs]
  | (E, ob) :: coreVCs =>
    have ⟨_, ctx, ts, t, smtVCs, hctx, hob, hrest⟩ := toSMTVCs_cons h
    simp only [denoteQueries, denoteProofObligations, hctx] at h ⊢
    match hp : denoteQuery ctx ts t with
    | none => simp_all
    | some p =>
      match hq : denoteProofObligation E ob with
      | none => simp_all
      | some q =>
        simp only [Option.bind_some, Option.bind_eq_bind]
        intro hP hQ
        have hpq := DPO_of_DQ hob hp hq
        apply DPOsGo_of_DQsGo hrest hP hQ hpq

theorem coreVCsCorrect_of_smtVCsCorrect (program : Program) :
    smtVCsCorrect program → coreVCsCorrect program := by
  simp only [coreVCsCorrect, smtVCsCorrect, genSMTVCs]
  match hb : genCoreVCs program with
  | none => simp_all
  | some coreVCs =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    match hs : toSMTVCs coreVCs with
    | none => simp_all
    | some smtVCs =>
      match hP : denoteQueries smtVCs with
      | none => simp_all
      | some P =>
        match hQ : denoteProofObligations coreVCs with
        | none =>
          have := DPOs_isSome_of_DQs_isSome hs (Option.isSome_of_eq_some hP)
          simp_all
        | some Q =>
          simp only [hP, Option.getD_some]
          exact DPOs_of_DQs hs hP hQ

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
deriving instance ToExpr for Core.Visibility
deriving instance ToExpr for Core.CoreExprMetadata
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

deriving instance ToExpr for Core.SMT.Context

deriving instance DecidableEq for Lambda.LConstr
deriving instance DecidableEq for Lambda.LDatatype

instance [DecidableEq α] : DecidableEq (Lambda.MutualDatatype α) :=
  inferInstance

instance [DecidableEq α] : DecidableEq (@Lambda.TypeFactory α) :=
  show DecidableEq (Array (Lambda.MutualDatatype α)) from inferInstance

deriving instance DecidableEq for Core.SMT.Context

def createGoal : SMTVC → MetaM MVarId := fun (label, ctx, ts, t) => do
  match translateQuery ctx ts t with
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

unsafe def genSMTVCs (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  let some program := type.app1? ``Strata.smtVCsCorrect | throwError "Expected a Strata.smtVCsCorrect goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrect
  let ovcs := .app (.const ``Strata.genSMTVCs []) program
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  trace[debug] m!"Generated {repr evcs}"
  let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs (toExpr (some evcs))
  -- let hEQVCs := mkApp2 (.const ``Eq.refl [1]) ovcsType (toExpr (some evcs))
  let hEQVCs ← nativeDecide eqVCs
  let r ← mv.rewrite (← mv.getType) hEQVCs
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  let mvs ← evcs.mapM SMT.createGoal
  trace[debug] m!"Created {mvs.length} SMT VC goals: {mvs}"
  let ps ← mvs.mapM MVarId.getType
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign hP
  return mvs

-- unsafe def genCoreVCs (mv : MVarId) : MetaM (List MVarId) := do
--   let type ← mv.getType
--   let some program := type.app1? ``Strata.coreVCsCorrect | throwError "Expected a Strata.coreVCsCorrect goal"
--   logInfo m!"Generating Core VCs for {program}"
--   let mv ← Meta.unfoldTarget mv ``Strata.coreVCsCorrect
--   let ovcs := .app (.const ``Strata.genCoreVCs []) program
--   let ovcsType := .app (.const ``Option [0]) (.const ``Core.coreVCs [])
--   let some evcs ← Meta.evalExpr (Option Core.coreVCs) ovcsType ovcs
--     | throwError "Failed to generate VCs"
--   logInfo m!"Generated Core VCs"
--   let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs (toExpr (some evcs))
--   -- let hEQVCs := mkApp2 (.const ``Eq.refl [1]) ovcsType (toExpr (some evcs))
--   let hEQVCs ← nativeDecide eqVCs
--   let r ← mv.rewrite (← mv.getType) hEQVCs
--   let mv ← mv.replaceTargetEq r.eNew r.eqProof
--   let mvs ← evcs.mapM SMT.createGoal
--   let ps ← mvs.mapM MVarId.getType
--   let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
--   mv.assign hP
--   return mvs

end Meta

namespace Tactic

syntax (name := genSMTVCs) "gen_smt_vcs" : tactic

open Lean Elab Tactic in
@[tactic genSMTVCs] unsafe def evalGenSMTVCs : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_smt_vcs) =>
    let mvs ← Meta.genSMTVCs (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

syntax (name := genCoreVCs) "gen_core_vcs" : tactic

open Lean Elab Tactic in
@[tactic genCoreVCs] unsafe def evalGenCoreVCs : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_core_vcs) =>
    let mvs ← Meta.genSMTVCs (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

end Tactic

end Strata
