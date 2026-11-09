/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.ObligationExtraction
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.LoopElim
import Strata.Transform.PrecondElim
import Strata.Transform.TerminationCheck
public import Strata.Languages.Core.SMTEncoder
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.SMT.Denote
public import Strata.DL.SMT.DenoteProps
import all Strata.Util.OrderedSet
import all Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramEval

-- For some reason shake wants to meta import the following
-- while lake itself only requires imports.

public meta import Strata.DL.SMT.Translate
import Strata.DL.SMT.Translate -- shake: keep
meta import Lean.Meta.Eval
import Lean.Meta.Eval -- shake: keep
import Lean.Meta.AppBuilder
import Lean.Meta.ProdN
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Lean.Meta.Tactic.Util

open Lean hiding Options

public section

namespace Strata.SMT

structure SanitizedContext where
  sorts : Array Strata.DL.SMT.Sort := #[]
  ufs : Array UF := #[]
  ifs : Array IF := #[]
  axms : Array Term := #[]
  tySubst : Map String TermType := []
deriving Repr, Inhabited, DecidableEq

def SanitizedContext.ofCore (ctx : Core.SMT.Context) : SanitizedContext :=
  { sorts := ctx.sorts.toArray, ufs := ctx.ufs.toArray, ifs := ctx.ifs.toArray,
    axms := ctx.axms.toArray, tySubst := ctx.tySubst }

def SanitizedContext.toCore (ctx : SanitizedContext) : Core.SMT.Context :=
  -- Build each OrderedKeyedSet with `ofArrayUnchecked`, not `ofArray`, so that
  -- `toList` of each field is exactly the stored array. Later kernel reduction
  -- of the denotation depends on this identity to recover the original fields.
  -- The fields come from `ofCore`, which are already deduped, so their keys are
  -- distinct and the no-duplicate-keys invariant `ofArrayUnchecked` assumes holds.
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
  -- Boole programs arrive with structured bodies and no calls. Mirror the
  -- prefix of `transformPipelinePhases` that still applies to them: termination
  -- checks for recursive functions and well-formedness checks for function
  -- preconditions (both add obligations the full `Core.verify` pipeline emits),
  -- then the loop phases, then the shared preSymbolicEvalPipelinePhases.
  -- Without `precondElimPipelinePhase`, any function declared with a
  -- `requires` makes `extractObligations` fail ("still carries a
  -- precondition"), so `gen_smt_vcs` silently produced no goals for such
  -- programs.
  let phases := [termCheckPipelinePhase, precondElimPipelinePhase,
                 insertLoopInvariantAssertsPipelinePhase, loopElimPipelinePhase]
                  ++ preSymbolicEvalPipelinePhases options
  -- Validate phase composition from Boole's guaranteed invariants (structured
  -- bodies, no calls).
  let _ ← (ValidatedPipeline.ofListFrom
              (factSet![.noCFGBodies, .noCalls]) phases).toOption
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

/-- Conjoin the denotations of `vcs` onto `p`. -/
noncomputable def denoteQueries.go (vcs : SMT.SMTVCs) (p : Prop) : Option Prop := do
  match vcs with
  | [] => return p
  | (_, ctx, ts, t) :: vcs =>
    let q ← denoteQuery ctx.toCore ts t
    go vcs (p ∧ q)

/--
Interpret a list of SMT verification conditions as the conjunction of their
denotations.
-/
noncomputable def denoteQueries (vcs : SMT.SMTVCs) : Option Prop := do
  match vcs with
  | [] => return True
  | (_, ctx, ts, t) :: vcs =>
    let p ← denoteQuery ctx.toCore ts t
    denoteQueries.go vcs p

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

/-! ### Characterizing `smtVCsCorrect`

These lemmas let a proof of `smtVCsCorrect` be assembled from one proof of
`denoteQuery ... = some P` per VC, without the kernel having to unfold
`smtVCsCorrect`, `denoteQueries` or `denoteQuery`.
-/

/-- Reduce `smtVCsCorrect` to a single proof of the conjoined denotation of all
VCs: if the VCs denote `Q` and `Q` holds, the program's VCs are correct. -/
theorem smtVCsCorrect_of (program : Program) (options : MetaVerifier.Options)
    (vcs : SMT.SMTVCs) (Q : Prop) (hgen : genSMTVCs program options = some vcs)
    (hq : denoteQueries vcs = some Q) (hQ : Q) : smtVCsCorrect program options := by
  simp [smtVCsCorrect, hgen, hq, hQ]

/-- The empty VC list denotes `True`. -/
theorem denoteQueries_nil : denoteQueries [] = some True := by
  simp [denoteQueries]

/-- Denoting a non-empty VC list folds the head VC's denotation into the
accumulating conjunction via `denoteQueries.go`. -/
theorem denoteQueries_cons (l : String) (sc : SMT.SanitizedContext) (ts : List SMT.Term)
    (t : SMT.Term) (vcs : SMT.SMTVCs) (p q : Prop)
    (h : denoteQuery sc.toCore ts t = some p) (hgo : denoteQueries.go vcs p = some q) :
    denoteQueries ((l, sc, ts, t) :: vcs) = some q := by
  simp [denoteQueries, h, hgo]

/-- With no remaining VCs, `denoteQueries.go` returns the accumulator. -/
theorem denoteQueries_go_nil (p : Prop) : denoteQueries.go [] p = some p := by
  simp [denoteQueries.go]

/-- `denoteQueries.go` conjoins the head VC's denotation onto the accumulator
and recurses on the tail. -/
theorem denoteQueries_go_cons (l : String) (sc : SMT.SanitizedContext) (ts : List SMT.Term)
    (t : SMT.Term) (vcs : SMT.SMTVCs) (p p' q : Prop)
    (h : denoteQuery sc.toCore ts t = some p') (hgo : denoteQueries.go vcs (p ∧ p') = some q) :
    denoteQueries.go ((l, sc, ts, t) :: vcs) p = some q := by
  simp [denoteQueries.go, h, hgo]

/-- Reduce `denoteQuery` on a sanitized context (via `toCore`) to
`denoteBoolTermFromContext` on the reversed context fields and the implication
of the axioms and assumptions over the conclusion. -/
theorem denoteQuery_toCore_of (sc : SMT.SanitizedContext) (assums : List SMT.Term)
    (conc : SMT.Term) (P : Prop)
    (h : denoteBoolTermFromContext sc.sorts.toList.reverse (mkISContext sc.tySubst).reverse
          sc.ufs.toList.reverse
          sc.ifs.toList.reverse
          (sc.axms.toList.foldr (.app .implies [·, ·] (.prim .bool))
            (assums.foldr (.app .implies [·, ·] (.prim .bool)) conc)) = some (PLift.up P)) :
    denoteQuery sc.toCore assums conc = some P := by
  apply SMT.DenoteProps.denoteQuery_of
  · rfl
  · simp [SMT.SanitizedContext.toCore]
  · simp [SMT.SanitizedContext.toCore]
  · exact h

theorem toSMTVCs_cons :
    toSMTVCs ((E, ob) :: coreVCs) options = some vcs →
    ∃ label ctx ts t smtVCs, vcs = (label, ctx, ts, t) :: smtVCs ∧
    Core.ProofObligation.toSMTObligation E ob options = some (label, ctx, ts, t) ∧
    toSMTVCs coreVCs options = some smtVCs := by
  simp only [toSMTVCs, Option.bind_eq_bind, Option.bind]
  grind

namespace SMT

instance {α : Type u} {β : Type v} [hu : ToLevel.{u}] [hv : ToLevel.{v}] [ToExpr α] [ToExpr β] : ToExpr (Map α β) where
  -- `Map` is an exposed synonym for `List`, so a list literal has type `Map α β`
  -- by unfolding. Avoid `Map.ofList`, which importers cannot unfold.
  toExpr m   := @toExpr _ (@instToExprListOfToLevel _ ToLevel.max.{u, v} _) m.toList
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

/--
Replace sort synonyms by their definitions, as `denoteQuery` does before
denoting a query. `translateQuery` would otherwise bind them with `let`, which
hides the definitions from operators that inspect the type of their operands
(e.g. the width of a bitvector).
-/
def substituteSynonyms (ctx : SanitizedContext) (ts : List Term) (t : Term) :
    SanitizedContext × List Term × Term :=
  let iss := (mkISContext ctx.tySubst).reverse
  if iss.isEmpty then (ctx, ts, t) else
    ({ ctx with tySubst := [], ufs := ctx.ufs.map (substituteUFIS iss),
                ifs := ctx.ifs.map (substituteIFIS iss), axms := ctx.axms.map (substituteTermIS iss) },
     ts.map (substituteTermIS iss), substituteTermIS iss t)

mutual

/-- Does the term apply a datatype constructor, tester or selector?  `denoteTerm`
    has no case for these, so a query containing one has no denotation. -/
private def Term.hasDatatypeOp (t : Term) : Bool :=
  match t with
  | .app (.datatype_op ..) _ _ => true
  | .app _ args _ => Term.anyHasDatatypeOp args
  | .quant _ _ trs body => body.hasDatatypeOp || Term.anyHasDatatypeOps trs
  | .some t => t.hasDatatypeOp
  | _ => false

private def Term.anyHasDatatypeOp (ts : List Term) : Bool :=
  match ts with
  | [] => false
  | t :: ts => t.hasDatatypeOp || Term.anyHasDatatypeOp ts

private def Term.anyHasDatatypeOps (tss : List (List Term)) : Bool :=
  match tss with
  | [] => false
  | ts :: rest => Term.anyHasDatatypeOp ts || Term.anyHasDatatypeOps rest

end

def createGoal : SMTVC → MetaM MVarId := fun (label, ctx, ts, t) => do
  if t.hasDatatypeOp || ts.any Term.hasDatatypeOp || ctx.axms.any Term.hasDatatypeOp
      || ctx.ifs.any (·.body.hasDatatypeOp) then
    throwError m!"gen_smt_vcs: verification condition '{label}' uses a datatype, which the \
      denotation of SMT queries does not cover yet, so no Lean goal can be created for it; \
      the SMT path still checks it"
  let (ctx, ts, t) := substituteSynonyms ctx ts t
  match translateQuery ctx.toCore ts t with
  | .error e =>
    -- Name the VC: the tactic must not drop an obligation it cannot state in
    -- Lean, so it fails, and the user should learn which obligation and why.
    throwError m!"gen_smt_vcs: cannot translate verification condition '{label}' to a Lean goal: {e}"
  | .ok e =>
    -- Hash-cons the goal: VCs from symbolic execution repeat subterms heavily,
    -- and the kernel caches its work on shared subterms.
    let e := ShareCommon.shareCommon' e
    trace[debug] "e := {e}"
    Meta.check e
    let .mvar mv ← Meta.mkFreshExprMVar e (userName := Translate.symbolToName label)
      | throwError "Failed to create goal"
    return mv

/-! ## Proof-producing translation

`proveQuery` builds a proof of `denoteQuery sc.toCore ts t = some P` by
chaining the lemmas of `Strata.SMT.DenoteProps`, following the structure of
`translateTerm`. Each step instantiates a lemma whose hypotheses are the
denotations of the subterms, so the kernel never evaluates the denotation.
The resulting `P` is the composition of the lemmas' semantic functions;
`gen_smt_vcs` checks that it is definitionally equal to the proposition built
by `translateQuery`, which only requires unfolding sort-level definitions,
projections and casts.
-/

namespace ProofGen

open Lean Meta


private def lem (n : Name) : Lean.Expr := .const (`Strata.SMT.DenoteProps ++ n) []

private def boolTrueRefl : Lean.Expr :=
  mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.true [])

private def boolFalseRefl : Lean.Expr :=
  mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.false [])

/-- `Eq.refl a` for `a : α` at universe `Sort u`. -/
private def mkRefl (u : Level) (α a : Lean.Expr) : Lean.Expr := mkApp2 (.const ``Eq.refl [u]) α a

/--
The elements of a list literal. `e` is put in weak head normal form only if it
is not already a `cons` or `nil`; `reduced` records that this was done.
-/
private partial def listElems (e : Lean.Expr) (reduced := false) : MetaM (List Lean.Expr) := do
  match_expr e with
  | List.cons _ a as => return a :: (← listElems as)
  | List.nil _ => return []
  | _ =>
    if reduced then throwError "proveQuery: expected a list literal, got{indentExpr e}"
    listElems (← whnf e) (reduced := true)

/-- The result of denoting a term: its type and the proof of its denotation. -/
structure Res where
  ty : TermType
  /-- The `TermDenoteResult` literal `⟨ty, h, ft⟩`. -/
  r : Lean.Expr
  /-- A proof of `denoteTerm ctx t = some r`. -/
  pf : Lean.Expr

instance : Inhabited Res := ⟨⟨.prim .bool, default, default⟩⟩

namespace Res
def tyE (r : Res) : Lean.Expr := r.r.getArg! 1
def hE (r : Res) : Lean.Expr := r.r.getArg! 2
def ftE (r : Res) : Lean.Expr := r.r.getArg! 3
end Res

/-- A proof of `lhs = rhs`. -/
structure EqProof where
  /-- The right-hand side of the proved equation. -/
  rhs : Lean.Expr
  /-- The proof of `lhs = rhs`. -/
  proof : Lean.Expr
deriving Inhabited

/-- A proof of `lhs = some rhs`, for an `Option`-valued `lhs`. -/
structure SomeEqProof where
  /-- The expression under `some` on the right-hand side of the proved equation. -/
  rhs : Lean.Expr
  /-- The proof of `lhs = some rhs`. -/
  proof : Lean.Expr
deriving Inhabited

/-- A proof of `∀ xs, lhs xs = fn xs`: the pointwise form of an `EqProof`
proved under the bound variables `xs`. -/
structure PointwiseEqProof where
  /-- The function `fun xs => rhs`. -/
  fn : Lean.Expr
  /-- The proof `fun xs => proof` of `∀ xs, lhs xs = fn xs`. -/
  proof : Lean.Expr
deriving Inhabited

/-- A context lookup: the index found and a proof of
`xs.findIdx? (· == key) = some idx`. -/
structure IdxProof where
  idx : Nat
  proof : Lean.Expr
deriving Inhabited

/-- The denotations of a list of terms and a proof of
`denoteTerms ctx ts = some results`, where `results` is the list literal of
their `TermDenoteResult`s. -/
structure ResultsProof where
  results : List Res
  proof : Lean.Expr
deriving Inhabited

/--
The type of a (possibly partial) lemma application `c a₁ … aₙ`, without
beta-reducing the arguments into it. `inferType` would beta-reduce, copying
each child's semantic function into its parent's, which is quadratic in the
depth of the term; here semantic functions stay shared.
-/
private def lemType (f : Lean.Expr) : MetaM Lean.Expr := do
  let args := f.getAppArgs
  let ty ← inferType f.getAppFn
  unless args.size ≤ ty.getNumHeadForalls do
    throwError "proveQuery: lemma applied to too many arguments{indentExpr f}"
  return (ty.getForallBodyMaxDepth args.size).instantiateRev args

/-- The right-hand side of the equation proved by the lemma application `pf`. -/
private def rhsOf (pf : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← lemType pf
  let some (_, _, rhs) := ty.eq? | throwError "proveQuery: expected an equation, got{indentExpr ty}"
  return rhs

private def mkRes (ty : TermType) (pf : Lean.Expr) : MetaM Res := do
  let rhs ← rhsOf pf
  let_expr Option.some _ r := rhs | throwError "proveQuery: expected `some`, got{indentExpr rhs}"
  return { ty, r, pf }

/-- Package a proof of `lhs = rhs`, reading `rhs` off its type. -/
private def EqProof.ofProof (pf : Lean.Expr) : MetaM EqProof :=
  return { rhs := ← rhsOf pf, proof := pf }

/-- Package a proof of `lhs = some rhs`, reading `rhs` off its type. -/
private def SomeEqProof.ofProof (pf : Lean.Expr) : MetaM SomeEqProof := do
  let rhs ← rhsOf pf
  let_expr Option.some _ v := rhs | throwError "proveQuery: expected `some`, got{indentExpr rhs}"
  return { rhs := v, proof := pf }

/-- Abstract the free variables `xs` of a proof of `lhs = rhs` into a proof of
`∀ xs, lhs = rhs`. -/
private def EqProof.abstract (xs : Array Lean.Expr) (e : EqProof) : MetaM PointwiseEqProof :=
  return { fn := ← mkLambdaFVars xs e.rhs, proof := ← mkLambdaFVars xs e.proof }

/--
For a partial application `f` of a lemma, skip `skip` further binders and
return the left-hand side of the equation in the next binder. Used to read off
the subgoal a "hypothesis-style" lemma expects before its earlier arguments
are known.
-/
private def hypLHS (f : Lean.Expr) (skip : Nat) : MetaM Lean.Expr := do
  let mut ty ← lemType f
  for _ in [0:skip] do
    let .forallE _ _ b _ := ty | throwError "proveQuery: lemma has too few binders"
    ty := b
  let .forallE _ hTy _ _ := ty | throwError "proveQuery: lemma has too few binders"
  let some (_, lhs, _) := hTy.eq? | throwError "proveQuery: expected an equation hypothesis{indentExpr hTy}"
  if lhs.hasLooseBVars then
    throwError "proveQuery: hypothesis depends on earlier binders{indentExpr lhs}"
  return lhs

/-- Lean-level mirror of the term context, used to compute lookup indices. -/
structure Env where
  vs : List TermVar
  ufs : List UF

/-- The key of a visited subterm: the term context it was denoted in and the
expression of the term. -/
structure TermKey where
  ctx : Lean.Expr
  term : Lean.Expr
deriving BEq, Hashable

/-- Caches shared by the proof producer across one query. -/
structure ProveState where
  /-- Cache of `findIdx?` proofs for UF lookups, keyed by UF. -/
  ufIdx : Std.HashMap UF IdxProof := {}
  /--
  Denotations of already visited subterms, keyed by the context and the term
  expression. VCs produced by symbolic execution repeat subterms heavily; with
  hash-consed term expressions, sharing them keeps the proof a DAG.
  -/
  terms : Std.HashMap TermKey Res := {}

/-- The proof producer's monad: `MetaM` with the caches in `ProveState`. -/
abbrev ProveM := StateRefT ProveState MetaM

/--
Prove `xsE.findIdx? (· == key) = some i`, where `xsE` evaluates to a list literal
whose elements correspond to `xs`.
-/
private partial def findIdxProof [BEq α] (headLem tailLem sameIdTailLem : Name) (idOf : α → String)
    (keyTy : Lean.Expr) (key : α) (keyE : Lean.Expr) (xs : List α) (xsE : Lean.Expr) :
    MetaM IdxProof := do
  let_expr List.cons _ xE restE := ← whnf xsE
    | throwError "proveQuery: symbol not found in context"
  match xs with
  | x :: xs =>
    if x == key then
      -- `x = key` by reflexivity; both are literals of the same value.
      return { idx := 0, proof := mkAppN (lem headLem) #[xE, restE, keyE, mkRefl 1 keyTy keyE] }
    else
      -- Skip `x`: by name if the names differ (`String` equality always
      -- reduces), otherwise by type or signature (`TermType.beq`).
      let skipLem := if idOf x == idOf key then sameIdTailLem else tailLem
      let rest ← findIdxProof headLem tailLem sameIdTailLem idOf keyTy key keyE xs restE
      return { idx := rest.idx + 1,
               proof := mkAppN (lem skipLem) #[xE, restE, keyE, mkRawNatLit rest.idx, boolFalseRefl, rest.proof] }
  | [] => throwError "proveQuery: symbol not found in context"

private def listExprOf (xsE : List Lean.Expr) (ty : Lean.Expr) (u : Level := 0) : Lean.Expr :=
  xsE.foldr (fun x acc => mkApp3 (.const ``List.cons [u]) ty x acc) (mkApp (.const ``List.nil [u]) ty)

private def resListType (ctx : Lean.Expr) : Lean.Expr := mkApp (.const ``TermDenoteResult []) ctx

/-- Chain `applyUF`/`applyUFAux` equations for the value of a UF application at
`tdi`: proves `lhs = v`. -/
private partial def applyUFChain (lhs : Lean.Expr) : MetaM EqProof := do
  -- lhs = @applyUF ctx args out h tdi uf as hal
  let args := lhs.getAppArgs
  let p₁ := mkAppN (lem `applyUF_eq) args
  let rest ← auxChain (← rhsOf p₁)
  return { rhs := rest.rhs, proof := ← mkEqTrans p₁ rest.proof }
where
  auxChain (e : Lean.Expr) : MetaM EqProof := do
    -- e = @applyUFAux ctx args out h tdi uf as hl has
    let e ← whnfCore e
    let args := e.getAppArgs
    let #[ctx, tys, out, h, tdi, uf, as, hl, has] := args
      | throwError "proveQuery: unexpected applyUFAux application{indentExpr e}"
    match_expr ← whnf as with
    | List.nil _ =>
      EqProof.ofProof (mkAppN (lem `applyUFAux_nil) #[ctx, out, h, tdi, uf, hl, has])
    | List.cons _ a as' =>
      let tys ← whnf tys
      let_expr List.cons _ ty tys' := tys | throwError "proveQuery: UF arity mismatch"
      let p := mkAppN (lem `applyUFAux_cons) #[ctx, ty, tys', out, h, tdi, uf, a, as', hl, has]
      let rest ← auxChain (← rhsOf p)
      return { rhs := rest.rhs, proof := ← mkEqTrans p rest.proof }
    | _ => throwError "proveQuery: expected a list literal of arguments"

/-- Eliminate `buildForall`/`buildExists`: proves `build ... = F`. -/
private partial def buildQuantChain (nilLem consLem : Name) (lhs : Lean.Expr) : MetaM EqProof := do
  let #[ctx, vs, hTys, fb] := lhs.getAppArgs
    | throwError "proveQuery: unexpected quantifier builder{indentExpr lhs}"
  match_expr ← whnfR vs with
  | List.nil _ =>
    EqProof.ofProof (mkAppN (lem nilLem) #[ctx, hTys, fb])
  | List.cons _ v vs' =>
    let f := mkAppN (lem consLem) #[ctx, v, vs', hTys, fb]
    let rest ← buildQuantChain nilLem consLem (← hypLHS f 1)
    EqProof.ofProof (mkAppN f #[rest.rhs, rest.proof])
  | _ => throwError "proveQuery: expected a literal list of bound variables"

/-- Chain `rightAssoc.go` equations: proves `rightAssoc.go ... = some g`. -/
private partial def rightAssocChain (lhs : Lean.Expr) : MetaM SomeEqProof := do
  -- lhs = rightAssoc.go ctx ty h op rs
  let #[ctx, ty, h, op, rsE] := lhs.getAppArgs | throwError "proveQuery: unexpected rightAssoc.go"
  match ← listElems rsE with
  | [r₁, r₂] =>
    SomeEqProof.ofProof (mkAppN (lem `rightAssoc_go_two)
      #[ctx, ty, h, op, r₁.getArg! 2, r₂.getArg! 2, r₁.getArg! 3, r₂.getArg! 3])
  | r₁ :: r₂ :: r₃ :: rest =>
    let restE := listExprOf rest (resListType ctx) 1
    let f := mkAppN (lem `rightAssoc_go_cons) #[ctx, ty, h, op, r₁.getArg! 2, r₁.getArg! 3, r₂, r₃, restE]
    let tail ← rightAssocChain (← hypLHS f 1)
    SomeEqProof.ofProof (mkAppN f #[tail.rhs, tail.proof])
  | _ => throwError "proveQuery: implication needs at least two operands"

private partial def lookupUF (env : Env) (ctx : Lean.Expr) (uf : UF) (ufE : Lean.Expr) :
    ProveM IdxProof := do
  if let some r := (← get).ufIdx[uf]? then return r
  let ufsE := ctx.proj `Context 1 |>.proj ``TermContext 1
  let r ← findIdxProof `findIdx_uf_head `findIdx_uf_tail `findIdx_uf_tail_sig UF.id (.const ``UF []) uf ufE env.ufs ufsE
  modify fun s => { s with ufIdx := s.ufIdx.insert uf r }
  return r

private partial def alignProof (ctx : Lean.Expr) (rs : List Res) (rsE : Lean.Expr) (tysE : List Lean.Expr) : MetaM Lean.Expr := do
  match rs, tysE with
  | [], [] => return mkApp (lem `argTypesAlign_nil) ctx
  | r :: rs, tyE :: tysE =>
    let_expr List.cons _ _ rsE' := ← whnfR rsE | throwError "proveQuery: expected a cons"
    let tysRest := listExprOf tysE (.const ``TermType [])
    let p ← alignProof ctx rs rsE' tysE
    let h := mkRefl 1 (.const ``TermType []) tyE
    return mkAppN (lem `argTypesAlign_cons) #[ctx, r.r, rsE', tyE, tysRest, h, p]
  | _, _ => throwError "proveQuery: UF arity mismatch"


/-- The width expression of a bitvector-typed denotation. -/
private def bvWidth (r : Res) : MetaM Lean.Expr := do
  let_expr TermType.prim p := ← whnf r.tyE | throwError "proveQuery: expected a bitvector"
  let_expr TermPrimType.bitvec n := ← whnf p | throwError "proveQuery: expected a bitvector"
  return n

/-- The `TermType` expressions of the keys and values of an array sort. -/
structure ArrayTypes where
  key : Lean.Expr
  val : Lean.Expr

/-- The key and value type expressions of an array-typed denotation. -/
private def arrayTypes (r : Res) : MetaM ArrayTypes := do
  let_expr TermType.constr _ args := ← whnf r.tyE | throwError "proveQuery: expected an array"
  let [key, val] ← listElems args | throwError "proveQuery: expected an array"
  return { key, val }

/-- Chain `leftAssoc.go` equations over the remaining operands: proves
`leftAssoc.go ... = some r`. -/
private partial def goChain (ctx ty h opF lhs : Lean.Expr) (rest : List Res) : MetaM SomeEqProof := do
  let ft := lhs.getArg! 4
  match rest with
  | [] =>
    SomeEqProof.ofProof (mkAppN (lem `leftAssoc_go_nil) #[ctx, ty, h, opF, ft])
  | r₁ :: rest =>
    let restE := listExprOf (rest.map (·.r)) (resListType ctx) 1
    let f := mkAppN (lem `leftAssoc_go_cons) #[ctx, ty, h, opF, ft, r₁.hE, r₁.ftE, restE]
    let tail ← goChain ctx ty h opF (← hypLHS f 1) rest
    return { rhs := tail.rhs, proof := mkAppN f #[tail.rhs, tail.proof] }

/-- Lemmas for bitvector operators on two operands of the same width, and
whether the result is boolean. -/
private def bvSameWidthLemma? : Op.BV → Option (Name × Bool)
  | .bvslt => some (`den_bvslt, true) | .bvsle => some (`den_bvsle, true)
  | .bvult => some (`den_bvult, true) | .bvsge => some (`den_bvsge, true)
  | .bvsgt => some (`den_bvsgt, true) | .bvule => some (`den_bvule, true)
  | .bvugt => some (`den_bvugt, true) | .bvuge => some (`den_bvuge, true)
  | .bvudiv => some (`den_bvudiv, false) | .bvurem => some (`den_bvurem, false)
  | .bvsdiv => some (`den_bvsdiv, false) | .bvsrem => some (`den_bvsrem, false)
  | .bvsaddo => some (`den_bvsaddo, true) | .bvssubo => some (`den_bvssubo, true)
  | .bvsmulo => some (`den_bvsmulo, true)
  | _ => none

/-- Lemmas for left-associative bitvector operators. -/
private def bvLeftAssocLemma? : Op.BV → Option Name
  | .bvadd => some `den_bvadd | .bvsub => some `den_bvsub | .bvmul => some `den_bvmul
  | .bvand => some `den_bvand | .bvor => some `den_bvor | .bvxor => some `den_bvxor
  | _ => none

/-- Prove `leftAssoc ctx ty h opF rs = some r` for at least two operands. -/
private def leftAssocChain (ctx ty h opF : Lean.Expr) (rs : List Res) : MetaM SomeEqProof := do
  let r₁ :: r₂ :: rest := rs | throwError "proveQuery: operator needs at least two operands"
  let restE := listExprOf (rest.map (·.r)) (resListType ctx) 1
  let f := mkAppN (lem `leftAssoc_cons2) #[ctx, ty, h, opF, r₁.hE, r₂.hE, r₁.ftE, r₂.ftE, restE]
  let go ← goChain ctx ty h opF (← hypLHS f 1) rest
  return { rhs := go.rhs, proof := mkAppN f #[go.rhs, go.proof] }

mutual

partial def proveTerm (env : Env) (ctx : Lean.Expr) (t : Term) (tE : Lean.Expr) : ProveM Res := do
  if let some r := (← get).terms[({ ctx, term := tE } : TermKey)]? then return r
  let r ← proveTermCore env ctx t tE
  modify fun s => { s with terms := s.terms.insert { ctx, term := tE } r }
  return r

partial def proveTermCore (env : Env) (ctx : Lean.Expr) (t : Term) (tE : Lean.Expr) : ProveM Res := do
  let tE ← whnfR tE
  match t with
  | .prim (.bool true) => mkRes (.prim .bool) (mkApp (lem `den_true) ctx)
  | .prim (.bool false) => mkRes (.prim .bool) (mkApp (lem `den_false) ctx)
  | .prim (.int _) =>
    let xE := tE.appArg!.appArg!
    mkRes (.prim .int) (mkApp2 (lem `den_int) ctx xE)
  | .prim (.bitvec (n := n) _) =>
    let p ← whnfR tE.appArg!
    mkRes (.prim (.bitvec n)) (mkApp3 (lem `den_bitvec) ctx (p.getArg! 0) (p.getArg! 1))
  | .prim (.string _) =>
    mkRes (.prim .string) (mkApp2 (lem `den_string) ctx (← whnfR tE.appArg!).appArg!)
  | .none ty =>
    mkRes (.option ty) (mkApp3 (lem `den_none) ctx tE.appArg! boolTrueRefl)
  | .some a =>
    let ra ← proveTerm env ctx a tE.appArg!
    mkRes (.option ra.ty) (mkAppN (lem `den_some) #[ctx, tE.appArg!, ra.tyE, ra.hE, ra.ftE, ra.pf])
  | .var v =>
    let #[vE] := tE.getAppArgs | throwError "proveQuery: bad var literal"
    let hi ← findIdxProof `findIdx_var_head `findIdx_var_tail `findIdx_var_tail_ty TermVar.id (.const ``TermVar []) v vE env.vs
      (ctx.proj `Context 1 |>.proj ``TermContext 0)
    mkRes v.ty (mkAppN (lem `den_var) #[ctx, vE, mkRawNatLit hi.idx, boolTrueRefl, hi.proof])
  | .app (.core (.uf uf)) as _ =>
    let #[opE, asE, tyE] := tE.getAppArgs | throwError "proveQuery: bad app literal"
    let ufE := (← whnfR opE).appArg!.appArg!
    let args ← proveTerms env ctx as asE
    let hi ← lookupUF env ctx uf ufE
    let rsE := listExprOf (args.results.map (·.r)) (resListType ctx) 1
    let hal ← alignProof ctx args.results rsE (← listElems (mkApp (.const ``UF.args []) ufE))
    let f := mkAppN (lem `den_uf) #[ctx, ufE, asE, tyE, mkRawNatLit hi.idx, boolTrueRefl, hi.proof, rsE, hal]
    -- app.proof : ∀ tdi, applyUF tdi (lookupUF hi tdi) rs hal = app.fn tdi
    let app ← forallBoundedTelescope (← lemType f) (some 3) fun xs _ => do
      let hFTy ← inferType xs[2]!
      forallBoundedTelescope hFTy (some 1) fun tdi body => do
        let some (_, lhs, _) := body.eq? | throwError "proveQuery: unexpected den_uf hypothesis"
        (← applyUFChain lhs).abstract tdi
    mkRes uf.out (mkAppN f #[app.fn, args.proof, app.proof])
  | .app op as _ =>
    let #[opE, asE, rtE] := tE.getAppArgs | throwError "proveQuery: bad app literal"
    let asEs ← listElems asE
    match op, as, asEs with
    | .core .not, [a], [aE] =>
      let ra ← proveTerm env ctx a aE
      mkRes (.prim .bool) (mkAppN (lem `den_not) #[ctx, aE, rtE, ra.hE, ra.ftE, ra.pf])
    | .core .ite, [c, a, b], [cE, aE, bE] =>
      let rc ← proveTerm env ctx c cE
      let ra ← proveTerm env ctx a aE
      let rb ← proveTerm env ctx b bE
      unless ra.ty == rb.ty do throwError "proveQuery: ite branches differ in type"
      mkRes ra.ty (mkAppN (lem `den_ite)
        #[ctx, cE, aE, bE, rtE, ra.tyE, rc.hE, rc.ftE, ra.hE, rb.hE, ra.ftE, rb.ftE, rc.pf, ra.pf, rb.pf])
    | .core .eq, [a, b], [aE, bE] =>
      let ra ← proveTerm env ctx a aE
      let rb ← proveTerm env ctx b bE
      unless ra.ty == rb.ty do throwError "proveQuery: equality between different types"
      mkRes (.prim .bool) (mkAppN (lem `den_eq)
        #[ctx, aE, bE, rtE, ra.tyE, ra.hE, rb.hE, ra.ftE, rb.ftE, ra.pf, rb.pf])
    | .num .le, [a, b], [aE, bE] => chain2 env ctx `den_le_op opE rtE a b aE bE
    | .num .lt, [a, b], [aE, bE] => chain2 env ctx `den_lt_op opE rtE a b aE bE
    | .num .ge, [a, b], [aE, bE] => chain2 env ctx `den_ge_op opE rtE a b aE bE
    | .num .gt, [a, b], [aE, bE] => chain2 env ctx `den_gt_op opE rtE a b aE bE
    | .core .and, _, _ => leftAssocOp env ctx `den_and_op opE asE rtE as (.prim .bool)
    | .core .or, _, _ => leftAssocOp env ctx `den_or_op opE asE rtE as (.prim .bool)
    | .num .add, _, _ => leftAssocOp env ctx `den_add_op opE asE rtE as (.prim .int)
    | .num .sub, _, _ => leftAssocOp env ctx `den_sub_op opE asE rtE as (.prim .int)
    | .num .mul, _, _ => leftAssocOp env ctx `den_mul_op opE asE rtE as (.prim .int)
    | .num .div, _, _ => leftAssocOp env ctx `den_div_op opE asE rtE as (.prim .int)
    | .num .neg, [a], [aE] =>
      let ra ← proveTerm env ctx a aE
      mkRes (.prim .int) (mkAppN (lem `den_neg) #[ctx, aE, rtE, ra.hE, ra.ftE, ra.pf])
    | .num .abs, [a], [aE] => unaryOp env ctx `den_abs a aE rtE (fun _ => pure #[]) (fun _ => .prim .int)
    -- bitvectors
    | .bv .bvneg, [a], [aE] => unaryOp env ctx `den_bvneg a aE rtE (fun r => return #[← bvWidth r]) id
    | .bv .bvnot, [a], [aE] => unaryOp env ctx `den_bvnot a aE rtE (fun r => return #[← bvWidth r]) id
    | .bv .bvnego, [a], [aE] =>
      unaryOp env ctx `den_bvnego a aE rtE (fun r => return #[← bvWidth r]) (fun _ => .prim .bool)
    | .bv .ubv_to_int, [a], [aE] =>
      unaryOp env ctx `den_ubv_to_int a aE rtE (fun r => return #[← bvWidth r]) (fun _ => .prim .int)
    | .bv .sbv_to_int, [a], [aE] =>
      unaryOp env ctx `den_sbv_to_int a aE rtE (fun r => return #[← bvWidth r]) (fun _ => .prim .int)
    | .bv (.zero_extend i), [a], [aE] =>
      let iE := (← whnfR (← whnfR opE).appArg!).appArg!
      unaryOp env ctx `den_zero_extend a aE rtE (fun r => return #[iE, ← bvWidth r])
        (fun | .prim (.bitvec n) => .prim (.bitvec (n + i)) | ty => ty)
    | .bv (.int_to_bv n), [a], [aE] =>
      let nE := (← whnfR (← whnfR opE).appArg!).appArg!
      unaryOp env ctx `den_int_to_bv a aE rtE (fun _ => pure #[nE]) (fun _ => .prim (.bitvec n))
    | .bv .bvshl, [a, b], [aE, bE] =>
      binaryOp env ctx `den_bvshl a b aE bE rtE (fun ra rb => return #[← bvWidth ra, ← bvWidth rb]) (fun t _ => t)
    | .bv .bvlshr, [a, b], [aE, bE] =>
      binaryOp env ctx `den_bvlshr a b aE bE rtE (fun ra rb => return #[← bvWidth ra, ← bvWidth rb]) (fun t _ => t)
    | .bv .bvashr, [a, b], [aE, bE] =>
      binaryOp env ctx `den_bvashr a b aE bE rtE (fun ra rb => return #[← bvWidth ra, ← bvWidth rb]) (fun t _ => t)
    | .bv .bvconcat, [a, b], [aE, bE] =>
      binaryOp env ctx `den_bvconcat a b aE bE rtE (fun ra rb => return #[← bvWidth ra, ← bvWidth rb])
        (fun | .prim (.bitvec n), .prim (.bitvec m) => .prim (.bitvec (n + m)) | t, _ => t)
    | .bv o, [a, b], [aE, bE] =>
      if let some lemName := bvLeftAssocLemma? o then
        return ← leftAssocBV env ctx lemName asE rtE as
      let some (lemName, isBool) := bvSameWidthLemma? o
        | throwError "proveQuery: unsupported operator {repr op}"
      binaryOp env ctx lemName a b aE bE rtE
        (fun ra rb => do
          unless ra.ty == rb.ty do throwError "proveQuery: bitvector operands differ in width"
          return #[← bvWidth ra])
        (fun t _ => if isBool then .prim .bool else t)
    | .bv o, _, _ =>
      let some lemName := bvLeftAssocLemma? o | throwError "proveQuery: unsupported operator {repr op}"
      leftAssocBV env ctx lemName asE rtE as
    -- strings
    | .str .str_length, [a], [aE] =>
      unaryOp env ctx `den_str_length a aE rtE (fun _ => pure #[]) (fun _ => .prim .int)
    | .str .str_concat, _, _ => leftAssocOp env ctx `den_str_concat_op opE asE rtE as (.prim .string)
    -- arrays
    | .arr .select, [x, i], [xE, iE] =>
      let rx ← proveTerm env ctx x xE
      let ri ← proveTerm env ctx i iE
      let .constr "Array" [k, v] := rx.ty | throwError "proveQuery: select on a non-array"
      unless ri.ty == k do throwError "proveQuery: select with a mistyped index"
      let tys ← arrayTypes rx
      mkRes v (mkAppN (lem `den_select)
        #[ctx, xE, iE, rtE, tys.key, tys.val, rx.hE, ri.hE, rx.ftE, ri.ftE, rx.pf, ri.pf])
    | .arr .store, [x, i, w], [xE, iE, wE] =>
      let rx ← proveTerm env ctx x xE
      let ri ← proveTerm env ctx i iE
      let rw ← proveTerm env ctx w wE
      let .constr "Array" [k, v] := rx.ty | throwError "proveQuery: store on a non-array"
      unless ri.ty == k && rw.ty == v do throwError "proveQuery: mistyped store"
      let tys ← arrayTypes rx
      mkRes rx.ty (mkAppN (lem `den_store)
        #[ctx, xE, iE, wE, rtE, tys.key, tys.val, rx.hE, ri.hE, rw.hE, rx.ftE, ri.ftE, rw.ftE, rx.pf, ri.pf, rw.pf])
    | .num .mod, [a, b], [aE, bE] =>
      let ra ← proveTerm env ctx a aE
      let rb ← proveTerm env ctx b bE
      mkRes (.prim .int) (mkAppN (lem `den_mod) #[ctx, aE, bE, rtE, ra.hE, rb.hE, ra.ftE, rb.ftE, ra.pf, rb.pf])
    | .core .implies, _, _ =>
      if as.length < 2 then throwError "proveQuery: implication needs at least two operands"
      let args ← proveTerms env ctx as asE
      let rsE := listExprOf (args.results.map (·.r)) (resListType ctx) 1
      let f := mkAppN (lem `den_implies) #[ctx, asE, rtE, rsE]
      -- binders: g, has, hg
      let chain ← rightAssocChain (← hypLHS f 2)
      mkRes (.prim .bool) (mkAppN f #[chain.rhs, args.proof, chain.proof])
    | _, _, _ => throwError "proveQuery: unsupported operator {repr op}"
  | .quant q vs _ b =>
    let #[_, vsE, trE, bE] := tE.getAppArgs | throwError "proveQuery: bad quantifier literal"
    let (denLem, nilLem, consLem) := match q with
      | .all => (`den_forall, `buildForall_nil, `buildForall_cons)
      | .exist => (`den_exists, `buildExists_nil, `buildExists_cons)
    let f := mkAppN (lem denLem) #[ctx, vsE, trE, bE, boolTrueRefl]
    -- binders: h fb F hb hF
    let bodyLHS ← hypLHS f 3
    let ctx' := bodyLHS.getArg! 0
    let rb ← proveTerm { env with vs := vs.reverse ++ env.vs } ctx' b bE
    unless rb.ty == .prim .bool do throwError "proveQuery: quantifier body is not boolean"
    let f := mkAppN f #[rb.hE, rb.ftE]
    let quant ← buildQuantChain nilLem consLem (← hypLHS f 2)
    mkRes (.prim .bool) (mkAppN f #[quant.rhs, rb.pf, quant.proof])
  | _ => throwError "proveQuery: unsupported term {repr t}"

partial def proveTerms (env : Env) (ctx : Lean.Expr) (ts : List Term) (tsE : Lean.Expr) :
    ProveM ResultsProof := do
  match ts with
  | [] => return { results := [], proof := mkApp (lem `denoteTerms_nil) ctx }
  | t :: ts =>
    let_expr List.cons _ tE tsE' := ← whnfR tsE | throwError "proveQuery: expected a list literal"
    let r ← proveTerm env ctx t tE
    let rest ← proveTerms env ctx ts tsE'
    let rsE := listExprOf (rest.results.map (·.r)) (resListType ctx) 1
    return { results := r :: rest.results,
             proof := mkAppN (lem `denoteTerms_cons) #[ctx, tE, tsE', r.r, rsE, r.pf, rest.proof] }

partial def chain2 (env : Env) (ctx : Lean.Expr) (opLem : Name) (opE rtE : Lean.Expr)
    (a b : Term) (aE bE : Lean.Expr) : ProveM Res := do
  let ra ← proveTerm env ctx a aE
  let rb ← proveTerm env ctx b bE
  let hop := mkApp2 (lem opLem) ctx rtE
  -- hop : ∀ as, denoteTerm ctx (.app op as rt) = (denoteTerms ctx as).bind (chainable ctx ty h rel)
  let (ty, h, rel) ← forallBoundedTelescope (← lemType hop) (some 1) fun _ body => do
    let some (_, _, rhs) := body.eq? | throwError "proveQuery: unexpected operator lemma"
    let args := rhs.appArg!.getAppArgs
    return (args[1]!, args[2]!, args[3]!)
  mkRes (.prim .bool) (mkAppN (lem `den_chain2)
    #[ctx, opE, aE, bE, rtE, ty, h, ra.hE, rb.hE, rel, ra.ftE, rb.ftE, hop, ra.pf, rb.pf])

partial def leftAssocOp (env : Env) (ctx : Lean.Expr) (opLem : Name) (opE asE rtE : Lean.Expr)
    (as : List Term) (expected : TermType) : ProveM Res := do
  if as.length < 2 then throwError "proveQuery: operator needs at least two operands"
  let args ← proveTerms env ctx as asE
  let rs := args.results
  unless rs.all (·.ty == expected) do throwError "proveQuery: operand type mismatch"
  let hop := mkApp3 (lem opLem) ctx rtE asE
  let some (_, _, rhs) := (← lemType hop).eq? | throwError "proveQuery: unexpected operator lemma"
  let la := rhs.appArg!
  let #[_, ty, h, opF] := la.getAppArgs | throwError "proveQuery: unexpected leftAssoc"
  let rsE := listExprOf (rs.map (·.r)) (resListType ctx) 1
  let chain ← leftAssocChain ctx ty h opF rs
  mkRes expected (mkAppN (lem `den_leftAssoc)
    #[ctx, opE, asE, rtE, ty, h, opF, rsE, chain.rhs, hop, args.proof, chain.proof])

/-- Left-associative bitvector operators: the width is that of the first operand. -/
partial def leftAssocBV (env : Env) (ctx : Lean.Expr) (opLem : Name) (asE rtE : Lean.Expr)
    (as : List Term) : ProveM Res := do
  if as.length < 2 then throwError "proveQuery: operator needs at least two operands"
  let args ← proveTerms env ctx as asE
  let rs := args.results
  let r₁ :: rest := rs | unreachable!
  unless rs.all (·.ty == r₁.ty) do throwError "proveQuery: operand type mismatch"
  let n ← bvWidth r₁
  let f := mkAppN (lem opLem) #[ctx, asE, rtE, n, r₁.hE, r₁.ftE, listExprOf (rest.map (·.r)) (resListType ctx) 1]
  -- binders: r has hl
  let #[_, ty, h, opF, _] := (← hypLHS f 2).getAppArgs | throwError "proveQuery: unexpected leftAssoc"
  let chain ← leftAssocChain ctx ty h opF rs
  mkRes r₁.ty (mkAppN f #[chain.rhs, args.proof, chain.proof])

/-- A unary operator lemma `den_X ctx a rt params h fa ha`. -/
partial def unaryOp (env : Env) (ctx : Lean.Expr) (lemName : Name) (a : Term) (aE rtE : Lean.Expr)
    (params : Res → MetaM (Array Lean.Expr)) (resTy : TermType → TermType) : ProveM Res := do
  let ra ← proveTerm env ctx a aE
  mkRes (resTy ra.ty) (mkAppN (lem lemName) (#[ctx, aE, rtE] ++ (← params ra) ++ #[ra.hE, ra.ftE, ra.pf]))

/-- A binary operator lemma `den_X ctx a b rt params h₁ h₂ fa fb ha hb`. -/
partial def binaryOp (env : Env) (ctx : Lean.Expr) (lemName : Name) (a b : Term) (aE bE rtE : Lean.Expr)
    (params : Res → Res → MetaM (Array Lean.Expr)) (resTy : TermType → TermType → TermType) : ProveM Res := do
  let ra ← proveTerm env ctx a aE
  let rb ← proveTerm env ctx b bE
  mkRes (resTy ra.ty rb.ty) (mkAppN (lem lemName)
    (#[ctx, aE, bE, rtE] ++ (← params ra rb) ++ #[ra.hE, rb.hE, ra.ftE, rb.ftE, ra.pf, rb.pf]))

end

/-- Close the term context: eliminate UF binders one at a time. Proves
`bindUFs ... = some ft'`. -/
private partial def bindUFsChain (lhs : Lean.Expr) : MetaM SomeEqProof := do
  -- lhs = bindUFs sctx vs ufs ft
  let #[sctx, vs, ufs, ft] := lhs.getAppArgs | throwError "proveQuery: unexpected bindUFs"
  match_expr ← whnfR ufs with
  | List.nil _ =>
    SomeEqProof.ofProof (mkAppN (lem `bindUFs_nil) #[sctx, vs, ft])
  | List.cons _ uf ufs' =>
    let f := mkAppN (lem `bindUFs_cons) #[sctx, vs, uf, ufs', ft, boolTrueRefl]
    let rest ← bindUFsChain (← hypLHS f 1)
    return { rhs := rest.rhs, proof := mkAppN f #[rest.rhs, rest.proof] }
  | _ => throwError "proveQuery: expected a literal list of UFs"

/-- Unfold `buildIFBody ctx vs bodyFt tdi` one bound parameter at a time.
Proves `buildIFBody ... tdi = v`. -/
private partial def buildIFBodyChain (lhs : Lean.Expr) : MetaM EqProof := do
  let #[ctx, vs, out, hTys, hTy, bodyFt, tdi] := lhs.getAppArgs
    | throwError "proveQuery: unexpected buildIFBody{indentExpr lhs}"
  match_expr ← whnfR vs with
  | List.nil _ =>
    EqProof.ofProof (mkAppN (lem `buildIFBody_nil) #[ctx, out, hTys, hTy, bodyFt, tdi])
  | List.cons _ v vs' =>
    let f := mkAppN (lem `buildIFBody_cons) #[ctx, v, vs', out, hTys, hTy, bodyFt]
    -- binders: G hrest tdi
    let rest ← forallBoundedTelescope (← lemType f) (some 2) fun xs _ => do
      forallBoundedTelescope (← inferType xs[1]!) (some 1) fun tdi' body => do
        let some (_, lhs', _) := body.eq? | throwError "proveQuery: unexpected buildIFBody_cons"
        (← buildIFBodyChain lhs').abstract tdi'
    EqProof.ofProof (mkAppN f #[rest.fn, rest.proof, tdi])
  | _ => throwError "proveQuery: expected a literal parameter list"

/--
Close the interpreted-function binders: denote each function body and push its
semantics into the environment. Proves `bindIFs ... = some ft'`.
-/
private partial def bindIFsChain (ufs : List UF) (ifs : List IF) (lhs : Lean.Expr) :
    MetaM SomeEqProof := do
  let #[sctx, vs, ufsE, ifsE, ft] := lhs.getAppArgs | throwError "proveQuery: unexpected bindIFs"
  match ifs with
  | [] =>
    return { rhs := ft, proof := mkAppN (lem `bindIFs_nil) #[sctx, vs, ufsE, ft] }
  | iF :: ifs' =>
    let_expr List.cons _ iFE ifsE' := ← whnfR ifsE | throwError "proveQuery: expected a list of functions"
    let f := mkAppN (lem `bindIFs_cons) #[sctx, vs, ufsE, iFE, ifsE', ft]
    -- binders: ft' ft'' h₁ h₂
    let #[_, ctxI, _] := (← hypLHS f 2).getAppArgs | throwError "proveQuery: unexpected bindIF"
    let g := mkAppN (lem `bindIF_eq) #[iFE, ctxI, ft, boolTrueRefl]
    -- binders: h bodyFt F hb hF
    let bodyCtx := (← hypLHS g 3).getArg! 0
    let bodyE ← whnf (mkApp (.const ``IF.body []) iFE)
    let env : Env := { vs := iF.args.reverse, ufs := ifs'.map IF.toUF ++ ufs }
    let (rb, _) ← (proveTerm env bodyCtx iF.body bodyE).run {}
    unless rb.ty == iF.out do throwError "proveQuery: body of {iF.id} has the wrong type"
    let g := mkAppN g #[rb.hE, rb.ftE]
    let body ← forallBoundedTelescope (← lemType g) (some 3) fun xs _ => do
      forallBoundedTelescope (← inferType xs[2]!) (some 1) fun tdi bodyTy => do
        let some (_, lhs', _) := bodyTy.eq? | throwError "proveQuery: unexpected bindIF_eq"
        (← buildIFBodyChain lhs').abstract tdi
    let bound ← SomeEqProof.ofProof (mkAppN g #[body.fn, rb.pf, body.proof])
    let f := mkApp f bound.rhs
    let rest ← bindIFsChain ufs ifs' (← hypLHS f 2)
    return { rhs := rest.rhs, proof := mkAppN f #[rest.rhs, bound.proof, rest.proof] }

/-- Close the sort context: eliminate uninterpreted-sort binders one at a time.
Proves `bindUSs ... = some ft'`. -/
private partial def bindUSsChain (lhs : Lean.Expr) : MetaM SomeEqProof := do
  -- lhs = bindUSs uss iss ft
  let #[uss, iss, ft] := lhs.getAppArgs | throwError "proveQuery: unexpected bindUSs"
  match_expr ← whnfR uss with
  | List.nil _ => return { rhs := ft, proof := mkAppN (lem `bindUSs_nil) #[iss, ft] }
  | List.cons _ us uss' =>
    let f := mkAppN (lem `bindUSs_cons) #[us, uss', iss, ft]
    let rest ← bindUSsChain (← hypLHS f 1)
    return { rhs := rest.rhs, proof := mkAppN f #[rest.rhs, rest.proof] }
  | _ => throwError "proveQuery: expected a literal list of sorts"

/--
Prove `denoteQuery sc.toCore ts t = some P` for a concrete query, returning
`P` as `rhs` with the proof. `scE`, `tsE` and `tE` are the expressions denoting
`sc`, `ts` and `t`.
-/
def proveQuery (sc : SanitizedContext) (scE : Lean.Expr) (ts : List Term) (tsE : Lean.Expr)
    (t : Term) (tE : Lean.Expr) : MetaM SomeEqProof := do
  let imp (a b : Term) : Term := .app .implies [a, b] (.prim .bool)
  let body := sc.axms.toList.foldr imp (ts.foldr imp t)
  let ufs := sc.ufs.toList.reverse
  let ifs := sc.ifs.toList.reverse
  -- Sort synonyms are substituted away before denotation.
  let iss := (mkISContext sc.tySubst).reverse
  let ufs' := if iss.isEmpty then ufs else ufs.map (substituteUFIS iss)
  let ifs' := if iss.isEmpty then ifs else ifs.map (substituteIFIS iss)
  let (body', bodyE, bodyE') ← if iss.isEmpty then
      -- Reuse the (shared) expressions of the axioms, assumptions and goal.
      let impE (a b : Lean.Expr) : Lean.Expr :=
        mkApp3 (.const ``Term.app []) (mkApp (.const ``Op.core []) (.const ``Op.Core.implies []))
          (listExprOf [a, b] (toTypeExpr Term)) (toExpr (TermType.prim .bool))
      let axmsE ← listElems (mkApp2 (.const ``Array.toList [0]) (toTypeExpr Term)
        (mkApp (.const ``SanitizedContext.axms []) scE))
      let bodyE := axmsE.foldr impE ((← listElems tsE).foldr impE tE)
      pure (body, bodyE, bodyE)
    else
      let body' := substituteTermIS iss body
      pure (body', toExpr body, ShareCommon.shareCommon' (toExpr body'))
  let ufsE' := toExpr ufs'
  let ifsE' := toExpr ifs'
  let f := mkAppN (lem `denoteBoolTermFromContext_of)
    #[toExpr sc.sorts.toList.reverse, toExpr iss, toExpr ufs, toExpr ifs, bodyE, ufsE', ifsE', bodyE']
  -- binders: h ft ft₁ ft₂ ft₃ hufs hifs htt ht hif huf hus
  let ctx := (← hypLHS f 8).getArg! 0
  let (r, _) ← (proveTerm { vs := [], ufs := ifs'.map IF.toUF ++ ufs' } ctx body' bodyE').run {}
  unless r.ty == .prim .bool do throwError "proveQuery: query is not boolean"
  let f := mkAppN f #[r.hE, r.ftE]
  let ifsClosed ← bindIFsChain ufs' ifs' (← hypLHS f 7)
  let f := mkApp f ifsClosed.rhs
  let ufsClosed ← bindUFsChain (← hypLHS f 7)
  let f := mkApp f ufsClosed.rhs
  let ussClosed ← bindUSsChain (← hypLHS f 7)
  -- The substitutions are checked by evaluation; with no synonyms the term is
  -- unchanged, which a lemma states without evaluating the term.
  let hufs := mkRefl 1 (toTypeExpr (List UF)) ufsE'
  let hifs := mkRefl 1 (toTypeExpr (List IF)) ifsE'
  let htt := if iss.isEmpty then mkApp (lem `substituteTermIS_nil) bodyE
    else mkRefl 1 (toTypeExpr Term) bodyE'
  let pDBT := mkAppN f #[ussClosed.rhs, hufs, hifs, htt, r.pf, ifsClosed.proof, ufsClosed.proof,
    ussClosed.proof]
  let some (_, _, rhs) := (← lemType pDBT).eq? | throwError "proveQuery: unexpected closure lemma"
  let_expr Option.some _ lifted := rhs | throwError "proveQuery: unexpected closure lemma"
  let P := lifted.appArg!
  return { rhs := P, proof := mkAppN (.const ``Strata.denoteQuery_toCore_of []) #[scE, tsE, tE, P, pDBT] }

end ProofGen

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

/--
Prove `denoteQuery sc.toCore ts t = some P` for the goal `P` built by
`translateQuery`, using the proof-producing translation. If that fails, report
an error naming the VC.
-/
def denoteQueryProof (label : String) (sc : SMT.SanitizedContext) (scE : Lean.Expr)
    (ts : List SMT.Term) (tsE : Lean.Expr) (t : SMT.Term) (tE : Lean.Expr) (P : Lean.Expr) :
    MetaM Lean.Expr := do
  let failure (why : MessageData) : MessageData :=
    m!"gen_smt_vcs: cannot prove that the goal for verification condition \
      '{label}' is its denotation: {why}"
  let den ← try SMT.ProofGen.proveQuery sc scE ts tsE t tE
    catch e => throwError failure e.toMessageData
  -- Check the match with the kernel: it is the same check the kernel
  -- performs on the final proof, and it is much faster than `Meta.isDefEq`.
  match Lean.Kernel.isDefEq (← getEnv) {} den.rhs P with
  | .ok true => pure ()
  | .ok false =>
    throwError failure m!"the denotation{indentExpr den.rhs}\ndoes not match the translated goal{indentExpr P}"
  | .error e =>
    throwError failure m!"the kernel raised an error while checking the denotation: {e.toMessageData (← getOptions)}"
  return den.proof

/-- The expressions of the components of a VC `(label, ctx, assumptions, goal)`. -/
private structure VCExprs where
  label : Lean.Expr
  ctx : Lean.Expr
  assums : Lean.Expr
  goal : Lean.Expr
deriving Inhabited

/-- The literal of the whole VC tuple. -/
private def VCExprs.toTuple (vc : VCExprs) : MetaM Lean.Expr :=
  return (← Lean.Meta.mkProdMkN #[vc.label, vc.ctx, vc.assums, vc.goal] 0).1

private unsafe def genSMTVCsUnsafe (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  let some (program, options) := type.app2? ``Strata.smtVCsCorrect
    | throwError "Expected a Strata.smtVCsCorrect goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let ovcs := mkApp2 (.const ``Strata.genSMTVCs []) program options
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  trace[debug] m!"Generated {repr evcs}"
  -- Build the VC list literal from per-component expressions so the
  -- expressions passed to the per-VC proofs are shared with it.
  let vcEs := evcs.map fun (l, sc, ts, t) =>
    ShareCommon.shareCommon'
      ({ label := toExpr l, ctx := toExpr sc, assums := toExpr ts, goal := toExpr t } : VCExprs)
  let vcTy := toTypeExpr Strata.SMT.SMTVC
  -- The literals of all suffixes of the VC list, longest first. They are
  -- shared with `evcsE`, so the chain proof below is linear in the number of VCs.
  let tails ← vcEs.foldrM (init := [mkApp (.const ``List.nil [0]) vcTy]) fun vc acc => do
    return mkApp3 (.const ``List.cons [0]) vcTy (← vc.toTuple) acc.head! :: acc
  let evcsE := tails.head!
  let hgen ← nativeDecide (mkApp3 (.const ``Eq [1]) ovcsType ovcs
    (mkApp2 (.const ``Option.some [0]) (.const ``Strata.SMT.SMTVCs []) evcsE))
  let mvs ← evcs.mapM SMT.createGoal
  trace[debug] m!"Created {mvs.length} SMT VC goals: {mvs}"
  let ps ← mvs.mapM MVarId.getType
  let hs ← (evcs.zip (vcEs.zip ps)).mapM fun ((l, sc, ts, t), vcE, P) =>
    denoteQueryProof l sc vcE.ctx ts vcE.assums t vcE.goal P
  -- `denoteQueries evcs = some (andN ps)`
  let q := andN ps
  -- Each VC is paired with the literal of the VCs after it.
  let rec goProof (vcs : List (VCExprs × Lean.Expr))
      (rest : List (Lean.Expr × Lean.Expr)) (p : Lean.Expr) : MetaM Lean.Expr := do
    match vcs, rest with
    | [], _ => return mkApp (.const ``Strata.denoteQueries_go_nil []) p
    | (vc, tailE) :: vcs, (p', h) :: rest =>
      let pp' := mkApp2 (.const ``And []) p p'
      let hgo ← goProof vcs rest pp'
      return mkAppN (.const ``Strata.denoteQueries_go_cons [])
        #[vc.label, vc.ctx, vc.assums, vc.goal, tailE, p, p', q, h, hgo]
    | _, [] => throwError "gen_smt_vcs: internal error"
  let pairs := ps.zip hs
  let hq ← match vcEs.zip tails.tail!, pairs with
    | [], _ => pure (.const ``Strata.denoteQueries_nil [])
    | (vc, tailE) :: vcs, (p, h) :: rest => do
      let hgo ← goProof vcs rest p
      pure <| mkAppN (.const ``Strata.denoteQueries_cons [])
        #[vc.label, vc.ctx, vc.assums, vc.goal, tailE, p, q, h, hgo]
    | _, [] => throwError "gen_smt_vcs: internal error"
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign (mkAppN (.const ``Strata.smtVCsCorrect_of []) #[program, options, evcsE, andN ps, hgen, hq, hP])
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

The goals are the propositions built by `translateQuery`, but the tactic does
not trust that translation: for each VC it also produces a proof that the
goal is the denotation (`denoteQuery`) of the VC, by chaining the lemmas in
`Strata.SMT.DenoteProps`. If that proof cannot be produced for some VC, the
tactic fails, naming the VC.
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
