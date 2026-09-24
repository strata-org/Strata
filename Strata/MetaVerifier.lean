/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.ObligationExtraction
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.LoopElim
public import Strata.Languages.C_Simp.C_Simp
public import Strata.Languages.Core.SMTEncoder
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.SMT.Denote
import Strata.Languages.C_Simp.DDMTransform.Translate
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramEval

-- For some reason shake wants to meta import the following
-- while lake itself only requires imports.

public meta import Strata.DL.SMT.Translate
import Strata.DL.SMT.Translate -- shake: keep
meta import Lean.Meta.Eval
import Lean.Meta.Tactic.Rewrite -- shake: keep
meta import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Unfold -- shake: keep
meta import Lean.Meta.Tactic.Unfold
import Lean.Meta.Eval -- shake: keep
import Lean.Meta.Constructions.CasesOn -- shake: keep

open Lean hiding Options

public section

namespace Strata.SMT

structure SanitizedContext where
  sorts : Array Strata.DL.SMT.Sort := #[]
  ufs : Array UF := #[]
  ifs : Array IF := #[]
  axms : Array Term := #[]
  tySubst : Map String TermType := []
  /-- The datatypes the query uses, in declaration order (`SMT.Datatypes` itself
      is not kernel-reducible, so only this plain projection travels to the
      tactic). -/
  datatypes : Array SanitizedDatatype := #[]
deriving Repr, Inhabited, DecidableEq

/-- The used datatypes of `ctx` as `SanitizedDatatype`s.  A datatype with a
    field whose sort has no SMT form is left out; the translation then reports
    it as an unknown sort. -/
private def sanitizedDatatypes (ctx : Core.SMT.Context) : Array SanitizedDatatype :=
  ctx.datatypes.factory.toList.foldl (init := #[]) fun acc block =>
    block.foldl (init := acc) fun acc d =>
      if !ctx.seenDatatypes.contains d.name then acc else
      let constrs? : Option (Array SanitizedConstr) := d.constrs.toArray.mapM fun c => do
        let fields ← c.args.toArray.mapM fun (f, ty) => do
          let (t, _) ← (Core.LMonoTy.toSMTType ty ctx).toOption
          pure (d.name ++ ".." ++ f.name, t)
        pure { name := c.name.name, fields }
      match constrs? with
      | some constrs => acc.push { name := d.name, constrs }
      | none => acc

def SanitizedContext.ofCore (ctx : Core.SMT.Context) : SanitizedContext :=
  { sorts := ctx.sorts.toArray, ufs := ctx.ufs.toArray, ifs := ctx.ifs.toArray,
    axms := ctx.axms.toArray, tySubst := ctx.tySubst, datatypes := sanitizedDatatypes ctx }

def SanitizedContext.toCore (ctx : SanitizedContext) : Core.SMT.Context :=
  -- Build each OrderedKeyedSet with `ofArrayUnchecked`, not `ofArray`.
  -- The reflection tactic `gen_smt_vcs` evaluates this context in the
  -- *kernel* and `ofArray` which uses `HashSet` insert-fold does not reduce.
  -- The fields come from `ofCore` which are already-deduped,
  -- so their keys are distinct and the invariant holds.
  { sorts := .ofArrayUnchecked ctx.sorts
    ufs := .ofArrayUnchecked ctx.ufs
    ifs := .ofArrayUnchecked ctx.ifs
    axms := .ofArrayUnchecked ctx.axms
    tySubst := ctx.tySubst
    datatypes := .empty
    seenDatatypes := {}
    datatypeFuns := {} }

abbrev SMTVC := String × SanitizedContext × List Term × Term
abbrev SMTVCs := List SMTVC

end Strata.SMT

namespace Core

abbrev CoreVC := Env × Imperative.ProofObligation Expression
abbrev coreVCs := List (Env × Imperative.ProofObligation Expression)

def genVCs (program : Program) (options : VerifyOptions := .default) : Option coreVCs := do
  -- Boole programs arrive with structured bodies and no calls; add loop phases
  -- before the shared preSymbolicEvalPipelinePhases.
  let phases := [insertLoopInvariantAssertsPipelinePhase, loopElimPipelinePhase]
                  ++ preSymbolicEvalPipelinePhases options
  -- Validate phase composition from Boole's guaranteed invariants (structured
  -- bodies, no calls, no internal func decls).
  let _ ← (ValidatedPipeline.ofListFrom
              (factSet![.noCFGBodies, .noCalls, .noInternalFuncDecl]) phases).toOption
  -- The factory is seeded with Core.Factory so monomorphizeFunctions can look
  -- up built-in polymorphic functions.
  let initState := { Transform.CoreTransformState.emp with factory := Core.Factory }
  let (monoProgram, monoState) ←
    phases.foldlM (init := (program, initState)) fun (prog, state) pp =>
      let (result, newState) :=
        Transform.runWith prog (fun q => do let (_, q') ← pp.transform q; return q') state
      result.toOption.map fun q' => (q', newState)
  -- symbolicEval (toCoreProofObligationProgram) runs separately so we can keep
  -- monoProgram for buildEnv, which needs the pre-symbolic-evaluation program.
  match Core.toCoreProofObligationProgram options monoProgram with
  | .error _ => none
  | .ok (oblProgram, _stats) =>
    match Core.ObligationExtraction.extractObligations oblProgram with
    | .error _ => none
    | .ok obligations =>
      let E := match Core.buildEnv options monoProgram monoState.factory with
        | .ok (initE, _) =>
          match Program.eval initE with
          | .ok (pEs, _) => pEs.head?.getD initE
          | .error _ => initE
        | .error _ => Env.init (empty_factory := true)
      return obligations.toList.map (fun ob => (E, ob))

end Core

namespace C_Simp

def genVCs (program : Strata.C_Simp.Program) (options : Core.VerifyOptions := .default) : Option Core.coreVCs := do
  let program := Strata.to_core program
  Core.genVCs program options

end C_Simp

namespace Strata

open StrataDDM

namespace MetaVerifier

/--
Options that affect the verification conditions generated by the metaverifier.

This is intentionally a small subset of `Core.VerifyOptions`: most of its
fields configure the solver, output, or pipeline stopping points, which have
no bearing on the generated VCs or their denotation.
-/
structure Options where
  /-- Use SMT-LIB Array theory for `Map` types instead of an uninterpreted
  sort with axiomatized `select`/`update` functions. -/
  useArrayTheory : Bool := true

/--
Interpret metaverifier options as options for the Core verification pipeline.
-/
def Options.toVerifyOptions (options : Options) : Core.VerifyOptions :=
  { Core.VerifyOptions.default with
    verbose := .quiet
    useArrayTheory := options.useArrayTheory }

end MetaVerifier

/--
Generate verification conditions for a `StrataDDM.Program` by translating it to the
appropriate frontend verifier and collecting its deferred proof obligations.

Note that this can be extended to new dialects by using
`unsafe/@[implemented_by]` as in [`StrataBoole.MetaVerifier`](https://github.com/strata-org/Strata-Boole).
-/
def genCoreVCs (program : Program)
    (options : MetaVerifier.Options := {}) : Option Core.coreVCs := do
  if program.dialect == "Core" then
    let (program, #[]) := TransM.run default (translateProgram program) | none
    Core.genVCs program options.toVerifyOptions
  else if program.dialect == "C_Simp" then
    let (program, #[]) := C_Simp.TransM.run default (C_Simp.translateProgram program.commands) | none
    C_Simp.genVCs program options.toVerifyOptions
  else
    none

/--
Remove solver-side caches that destabilize definitional equality in metaprograms.

At the moment this is semantically harmless for denotation because
`Strata.DL.SMT.Denote.denoteQuery` rejects contexts with datatype machinery
(`datatypes`, `seenDatatypes`, `datatypeFuns`) populated anyway.
-/
private def sanitizeSMTContext (ctx : Core.SMT.Context) : SMT.SanitizedContext :=
  SMT.SanitizedContext.ofCore ctx

def Core.ProofObligation.toSMTObligation (E : Core.Env) (ob : Imperative.ProofObligation Core.Expression)
  (options : MetaVerifier.Options := {}) :
  Option SMT.SMTVC := do
    -- Seed the encoding context with the env's datatypes and the array-theory flag.
    let smtCtx := { Core.SMT.Context.default with
      datatypes := .ofFactory E.datatypes, useArrayTheory := options.useArrayTheory }
    -- Encode this single obligation from a fresh encoder state.
    let encState : Core.SMTEncodeState := .init { ctx := smtCtx }
    let maybeTerms := Core.encodeObligationToSMT E.factory encState ob
    match maybeTerms with
    | .error _ => none
    | .ok ({ assumptions := ts, varDefs, goal := t, ctx, .. }, _) =>
      -- For denotational semantics, variable definitions are equivalent to equalities
      let defAssumptions := varDefs.map fun d =>
        Strata.SMT.Factory.eq (.app (.uf ⟨d.name, [], d.ty⟩) [] d.ty) d.body
      (ob.label, sanitizeSMTContext ctx, defAssumptions ++ ts, t)

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

def toSMTVCs (vcs : Core.coreVCs)
    (options : MetaVerifier.Options := {}) : Option SMT.SMTVCs := do
  match vcs with
  | [] => return []
  | (E, ob) :: vcs =>
    let (label, ctx, ts, t) ← Core.ProofObligation.toSMTObligation E ob options
    let vcs ← toSMTVCs vcs options
    return (label, ctx, ts, t) :: vcs

/--
Generate SMT verification conditions for a `StrataDDM.Program`.
-/
def genSMTVCs (program : Program)
    (options : MetaVerifier.Options := {}) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCs program options
  toSMTVCs coreVCs options

/--
State semantic correctness of the SMT verification conditions generated for a
program under the given metaverifier options. For example,
`options.useArrayTheory` selects how the SMT encoder treats `Map` types: under
`true` they become SMT-LIB arrays, under `false` an uninterpreted sort with
axiomatized `select`/`update` functions.
-/
def smtVCsCorrect (program : Program)
    (options : MetaVerifier.Options := {}) : Prop :=
  match genSMTVCs program options with
  | some vcs => (denoteQueries vcs).getD False
  | none     => False

theorem toSMTVCs_cons :
    toSMTVCs ((E, ob) :: coreVCs) options = some vcs →
    ∃ label ctx ts t smtVCs, vcs = (label, ctx, ts, t) :: smtVCs ∧
    Core.ProofObligation.toSMTObligation E ob options = some (label, ctx, ts, t) ∧
    toSMTVCs coreVCs options = some smtVCs := by
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
deriving instance ToExpr for Strata.DL.SMT.Sort
deriving instance ToExpr for IF
deriving instance ToExpr for SanitizedConstr
deriving instance ToExpr for SanitizedDatatype
deriving instance ToExpr for SanitizedContext
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

/-- Namespace of the generated datatype declarations: `<current decl>.DT` when
    inside a declaration (the kernel restricts declarations added during
    elaboration to that prefix), `Strata.SMT.DT` otherwise. -/
def datatypeNamespace : CoreM Name :=
  return ((← getEnv).asyncPrefix?.getD `Strata.SMT) ++ `DT

/-- Lean declarations for the datatypes of a query, generated once per datatype
    (skipped when `ns.<name>` already exists).  For each datatype, in
    declaration order so that field types of earlier datatypes resolve:

    * `inductive ns.<d>` with the constructors and their fields;
    * a tester `is_<c> : ns.<d> → Prop` per constructor and a selector
      `<field> : ns.<d> → σ` per field, both by `casesOn`.

    SMT-LIB leaves a selector applied to another constructor unspecified, so a
    verification condition is valid only if it holds whatever that value is.
    Each selector therefore falls back to an `opaque` constant of its own: a
    proof can say nothing about it, and two selectors do not collapse onto the
    same value.  The witness such a declaration needs is the datatype's first
    constructor whose fields all have one.

    Strata also generates an eliminator for a datatype, encoding its induction
    principle.  That is not translated; only constructors, testers and
    selectors are. -/
def ensureDatatypeDecls (ns : Lean.Name) (dts : Array SanitizedDatatype) : MetaM Unit := do
  let mut witnesses : Std.HashMap Lean.Name Lean.Expr := {}
  for dt in dts do
    let tyName := SanitizedDatatype.typeName ns dt.name
    let sortExpr (t : TermType) : MetaM Lean.Expr :=
      Lean.ofExcept ((Translate.withDatatypes ns dts (Translate.translateSort t)).run' {})
    -- default witness: first constructor whose fields all have a default
    -- (a nullary one for the datatypes Strata generates); kept in `witnesses`
    -- rather than as an `Inhabited` instance, which cannot be registered from
    -- inside a declaration's elaboration.  Computed even when the datatype
    -- was declared by an earlier goal, since later datatypes' selectors need it.
    let dflt (ws : Std.HashMap Lean.Name Lean.Expr) (σ : Lean.Expr) : MetaM (Option Lean.Expr) := do
      if let .const n [] := σ then
        if let some w := ws[n]? then return some w
      try pure (some (← Meta.mkAppOptM ``Inhabited.default #[σ, none]))
      catch _ => pure none
    let mut witness : Option Lean.Expr := none
    for c in dt.constrs do
      if witness.isSome then break
      let fieldTys ← c.fields.toList.mapM (fun (_, σ) => sortExpr σ)
      let defaults? ← fieldTys.mapM (dflt witnesses)
      if defaults?.all Option.isSome then
        witness := some (mkAppN (.const (SanitizedDatatype.ctorName ns dt.name c.name) [])
                           (defaults?.filterMap id).toArray)
    let some w := witness
      | throwError m!"gen_smt_vcs: no default element for datatype '{dt.name}'"
    witnesses := witnesses.insert tyName w
    if (← getEnv).contains tyName then continue
    -- the inductive
    let ctors ← dt.constrs.toList.mapM fun c => do
      let fieldTys ← c.fields.toList.mapM (fun (_, σ) => sortExpr σ)
      let ty := fieldTys.foldr (fun σ acc => Lean.Expr.forallE .anonymous σ acc .default) (.const tyName [])
      pure ({ name := SanitizedDatatype.ctorName ns dt.name c.name, type := ty } : Constructor)
    addDecl <| .inductDecl [] 0
      [{ name := tyName, type := .sort (.succ .zero), ctors }] false
    -- realizations (equation lemmas, `noConfusion`, ...) are opt-in for
    -- declarations added programmatically
    enableRealizationsForConst tyName
    for c in ctors do enableRealizationsForConst c.name
    mkCasesOn tyName
    let dtTy : Lean.Expr := .const tyName []
    let addDefn (n : Lean.Name) (ty val : Lean.Expr) : MetaM Unit := do
      addDecl <| .defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe }
      enableRealizationsForConst n
    -- casesOn with an explicit motive; minor premises built per constructor
    let casesOn (motiveLvl : Lean.Level) (motive : Lean.Expr) (x : Lean.Expr) (minors : Array Lean.Expr) : Lean.Expr :=
      mkAppN (.const (tyName ++ `casesOn) [motiveLvl]) (#[motive, x] ++ minors)
    let minorFor (c : SanitizedConstr) (body : Array Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
      let fieldTys ← c.fields.toList.mapM (fun (_, σ) => sortExpr σ)
      let decls := (c.fields.toList.zip fieldTys).map fun ((sel, _), σ) =>
        (Lean.Name.mkSimple (match sel.splitOn ".." with | [_, f] => f | _ => sel), fun _ => pure σ)
      Meta.withLocalDeclsD decls.toArray fun fvars => do Meta.mkLambdaFVars fvars (← body fvars)
    -- testers
    for c in dt.constrs do
      let minors ← dt.constrs.mapM fun c' => minorFor c' fun _ =>
        pure (.const (if c'.name == c.name then ``True else ``False) [])
      let value ← Meta.withLocalDeclD `x dtTy fun x => do
        Meta.mkLambdaFVars #[x] (casesOn (.succ .zero) (.lam `_ dtTy (.sort .zero) .default) x minors)
      addDefn (SanitizedDatatype.testerName ns dt.name c.name) (.forallE `x dtTy (.sort .zero) .default) value
    -- selectors
    for c in dt.constrs do
      for ((sel, σt), k) in c.fields.toList.zip (List.range c.fields.size) do
        let σ ← sortExpr σt
        let selName := SanitizedDatatype.selectorName ns dt.name sel
        -- The witness is only what an `opaque` declaration needs to exist; it
        -- is invisible to a proof, which is the point.
        let some wσ ← dflt witnesses σ
          | throwError m!"gen_smt_vcs: no element to witness the unspecified result \
                          of selector '{sel}'"
        let unspecName := selName ++ `unspec
        unless (← getEnv).contains unspecName do
          addDecl <| .opaqueDecl { name := unspecName, levelParams := [], type := σ,
                                   value := wσ, isUnsafe := false, all := [unspecName] }
        let d : Lean.Expr := .const unspecName []
        let minors ← dt.constrs.mapM fun c' => minorFor c' fun fvars =>
          pure (if c'.name == c.name then fvars[k]! else d)
        let value ← Meta.withLocalDeclD `x dtTy fun x => do
          Meta.mkLambdaFVars #[x] (casesOn (.succ .zero) (.lam `_ dtTy σ .default) x minors)
        addDefn selName (.forallE `x dtTy σ .default) value

def createGoal : SMTVC → MetaM MVarId := fun (label, ctx, ts, t) => do
  let ns ← datatypeNamespace
  ensureDatatypeDecls ns ctx.datatypes
  match translateQuery ctx.toCore ts t ctx.datatypes ns with
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
  let some (program, options) := type.app2? ``Strata.smtVCsCorrect
    | throwError "Expected a Strata.smtVCsCorrect goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrect
  let ovcs := mkApp2 (.const ``Strata.genSMTVCs []) program options
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
  let mvType ← mv.getType
  let bridgeType := Lean.Expr.forallE `h (andN ps) mvType .default
  let bridgeName ← Lean.mkAuxDeclName `_genSMTVCs_tcbBridge
  Lean.addDecl (Declaration.axiomDecl {
    name := bridgeName, levelParams := [], type := bridgeType, isUnsafe := false
  })
  mv.assign (mkApp (.const bridgeName []) hP)
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
