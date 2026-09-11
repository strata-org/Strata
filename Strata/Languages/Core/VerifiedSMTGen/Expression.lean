/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.CoreOp
import all Strata.Languages.Core.CoreOp
public import Strata.Languages.Core.NameMangling
import all Strata.Languages.Core.NameMangling
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote

/-!
# Refactored SMT encoder — source Core-Expression language (typing + denotation)

The SOURCE expression fragment (`Expression.Expr` over `CoreLParams`) that both `ProofObligation` and
`CoreCtx` range over: its typing judgment (`HasSimpType`) and denotation (`simpDenote`), plus the
`collectArrowTy` helper the typing rules use to decompose fvar/op arrow types. SMT-free (no
`TermType`/`tyToTermType`/`Factory`).

Key results: `HasSimpType_implies_HasTypeA` (bridge to the context-free judgment), `collectArrowTy_foldr`,
and the `OpInterpConsistent` bundle.
-/

open Core Lambda Std

namespace Core.Refactor

/-! ## Arrow-type decomposition (copied from the encoder — the typing judgment below
references it to split an fvar/op's stored arrow type into `(args, ret)`).
-/

/-- Split an arrow type into its argument types and final return type. -/
def collectArrowTy : LMonoTy → List LMonoTy × LMonoTy
  | .tcons "arrow" [ty1, ty2] =>
    let (atys, rty) := collectArrowTy ty2
    (ty1 :: atys, rty)
  | ty => ([], ty)

/-- The de-Bruijn substitution turning a factory function's formal parameters into `.bvar`s. Shared by
    the encoder (lifting a `define-fun` body before translation) and the `ProofObligation`/factory
    well-formedness layer (`FactoryFnsWF`, `ModelRespects`). -/
def funcBvarSubst (f : LFunc CoreLParams) : Map CoreLParams.Identifier Expression.Expr :=
  Map.ofList ((List.range f.inputs.length).map
    (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr))))

/-! ## Monomorphic type restrictions + predefined-operator typing -/

inductive LExpr.MonoTyIsBase : LMonoTy → Prop where
  | bool : MonoTyIsBase (.tcons "bool" [])
  | int : MonoTyIsBase (.tcons "int" [])
  | string : MonoTyIsBase (.tcons "string" [])
  | bitvec : MonoTyIsBase (.bitvec n)

inductive LExpr.CoreOpHasType : CoreOp → List LMonoTy → LMonoTy → Prop where
  -- Unary int
  | intNeg : CoreOpHasType (.numeric ⟨.int, .Neg⟩) [.tcons "int" []] (.tcons "int" [])
  -- Unary bool
  | boolNot : CoreOpHasType (.bool .Not) [.tcons "bool" []] (.tcons "bool" [])
  -- Binary int → int
  | intAdd : CoreOpHasType (.numeric ⟨.int, .Add⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intSub : CoreOpHasType (.numeric ⟨.int, .Sub⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intMul : CoreOpHasType (.numeric ⟨.int, .Mul⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intDiv : CoreOpHasType (.numeric ⟨.int, .Div⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  | intMod : CoreOpHasType (.numeric ⟨.int, .Mod⟩) [.tcons "int" [], .tcons "int" []] (.tcons "int" [])
  -- Binary int → bool (comparisons)
  | intLt : CoreOpHasType (.numeric ⟨.int, .Lt⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intLe : CoreOpHasType (.numeric ⟨.int, .Le⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intGt : CoreOpHasType (.numeric ⟨.int, .Gt⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  | intGe : CoreOpHasType (.numeric ⟨.int, .Ge⟩) [.tcons "int" [], .tcons "int" []] (.tcons "bool" [])
  -- Binary bool → bool
  | boolAnd : CoreOpHasType (.bool .And) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolOr : CoreOpHasType (.bool .Or) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolImplies : CoreOpHasType (.bool .Implies) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])
  | boolEquiv : CoreOpHasType (.bool .Equiv) [.tcons "bool" [], .tcons "bool" []] (.tcons "bool" [])

/-- Whether a Core operator name denotes a *predefined* operator — decidably, by parsing the demangled
    base name with `CoreOp.ofString` and checking it is a RECOGNISED `CoreOp` (anything but the `.other`
    catch-all). This covers not just the int/bool ops (`CoreOpHasType`) but ALSO the Map/sequence/regex/
    bitvec/trigger ops that `CoreOp.ofString` recognises — exactly the operators the encoder handles
    natively and the collect walk skips. A monomorphized `$__mono#…` instance still classifies (via the
    demangle). uAT-free: recognition is `CoreOp.ofString`, independent of Array theory. -/
def isPredefinedOp (name : String) : Bool :=
  match CoreOp.ofString (Core.NameMangling.demangledBaseName name) with
  | .other _ => false
  | _ => true

/-! ## Typing judgment on `Expression.Expr` with n-ary free-variable / operator application
`Φ` = free-variable (arrow-capable) namespace; `Ψ` = user-function namespace; `Δ` = bvar types.
-/

abbrev FNameCtx := List (String × LMonoTy)
abbrev FVarCtx := FNameCtx
abbrev FnCtx := FNameCtx

mutual
inductive LExpr.HasSimpType (Φ : FVarCtx) (Ψ : FnCtx) : List LMonoTy → Expression.Expr → LMonoTy → Prop where
  | const c : MonoTyIsBase c.ty → HasSimpType Φ Ψ Δ (.const () c) c.ty
  | bvar i τ : Δ[i]? = some τ → MonoTyIsBase τ → HasSimpType Φ Ψ Δ (.bvar () i) τ
  | app fn arg rty : LExpr.AppSpine Φ Ψ Δ (.app () fn arg) [] rty →
    HasSimpType Φ Ψ Δ (.app () fn arg) rty
  | fvarNullary f τ rty : LExpr.AppSpine Φ Ψ Δ (.fvar () f (some τ)) [] rty →
    HasSimpType Φ Ψ Δ (.fvar () f (some τ)) rty
  | ite c t τ e : HasSimpType Φ Ψ Δ c (.tcons "bool" []) → HasSimpType Φ Ψ Δ t τ →
    HasSimpType Φ Ψ Δ e τ → HasSimpType Φ Ψ Δ (.ite () c t e) τ
  | eq e1 e2 τ : MonoTyIsBase τ → HasSimpType Φ Ψ Δ e1 τ → HasSimpType Φ Ψ Δ e2 τ →
    HasSimpType Φ Ψ Δ (.eq () e1 e2) (.tcons "bool" [])
  | quant qty body k name tr τ_tr : MonoTyIsBase qty →
    HasSimpType Φ Ψ (qty :: Δ) tr τ_tr →
    HasSimpType Φ Ψ (qty :: Δ) body (.tcons "bool" []) →
    HasSimpType Φ Ψ Δ (.quant () k name (some qty) tr body) (.tcons "bool" [])

/-- Application-spine judgment. `AppSpine Φ Ψ Δ e acc rty` types the head-spine `e`
    applied to `e`'s own arguments followed by `acc` more arguments. -/
inductive LExpr.AppSpine (Φ : FVarCtx) (Ψ : FnCtx) : List LMonoTy → Expression.Expr → List LMonoTy → LMonoTy → Prop where
  | app fn arg aty acc rty : LExpr.HasSimpType Φ Ψ Δ arg aty →
    LExpr.AppSpine Φ Ψ Δ fn (aty :: acc) rty →
    LExpr.AppSpine Φ Ψ Δ (.app () fn arg) acc rty
  | fvar f τ acc rty : (f.name, τ) ∈ Φ → collectArrowTy τ = (acc, rty) →
    MonoTyIsBase rty → LExpr.AppSpine Φ Ψ Δ (.fvar () f (some τ)) acc rty
  | op o oty acc rty : CoreOpHasType (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) acc rty →
    collectArrowTy oty = (acc, rty) →
    LExpr.AppSpine Φ Ψ Δ (.op () o (some oty)) acc rty
  | fnOp o oty acc rty : (o.name, oty) ∈ Ψ →
      isPredefinedOp o.name = false →
      collectArrowTy oty = (acc, rty) →
      MonoTyIsBase rty →
      LExpr.AppSpine Φ Ψ Δ (.op () o (some oty)) acc rty
end

/-! ## Denotation of the source fragment (`simpDenote`), gated on `LExpr.HasTypeA` -/

noncomputable def simpTcInterp : Lambda.TyConstrInterp := fun _ _ => Unit

instance : Lambda.TyConstrInterp.AllInhabited simpTcInterp where
  inhabited := fun _ _ => ⟨()⟩

def simpTyVarVal : Lambda.TyVarVal := fun _ => .tcons "bool" []

abbrev BVarCtx := List LMonoTy

noncomputable def simpDenote
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {Δ : BVarCtx}
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (e : Expression.Expr) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ)
    : Lambda.TyDenote simpTcInterp simpTyVarVal τ :=
  LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e τ h

/-- Apply a curried Lambda value of arrow type to a `BVarVal` — shared by the CoreCtx and ProofObligation
    define-fun consistency conditions. -/
def applyBVarVal : (argTys : List LMonoTy) → (ret : LMonoTy) →
    Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow ret argTys) →
    Lambda.BVarVal simpTcInterp simpTyVarVal argTys →
    Lambda.TyDenote simpTcInterp simpTyVarVal ret
  | [], _, f, .nil => f
  | _ :: _, ret, f, .cons x xs => applyBVarVal _ ret (f x) xs

/-! ## Load-bearing metatheory: `HasSimpType` ⟹ `HasTypeA`
(The WF/denotation DEFINITIONS in the language files gate `simpDenote` on the
`HasTypeA` produced here, so this bridge — and its two dependencies — must be
available already; the remaining `HasSimpType` metatheory is proof-phase.)
-/

/-- `collectArrowTy` inverts `List.foldr LMonoTy.arrow`. -/
theorem collectArrowTy_foldr (τ : LMonoTy) :
    let (args, ret) := collectArrowTy τ
    τ = List.foldr LMonoTy.arrow ret args := by
  fun_induction collectArrowTy τ with
  | case1 ty1 ty2 atys rty hc ih =>
    rw [hc] at ih
    simp only at ih
    simp only [List.foldr, LMonoTy.arrow]
    rw [← ih]
  | _ => rfl

mutual
/-- Every expression well-typed under the richer `HasSimpType` judgment (with free-variable and
    function contexts) is also well-typed under the context-free `HasTypeA` judgment that denotation
    uses. -/
theorem HasSimpType_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (h : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.HasTypeA Δ e τ := by
  match h with
  | .const c hbase => exact .const
  | .bvar i _ hlook hbase => exact .bvar hlook
  | .app fn arg rty hspine => exact AppSpine_implies_HasTypeA hspine
  | .fvarNullary f _ rty hspine => exact AppSpine_implies_HasTypeA hspine
  | .ite c t _ e_ hc ht hee =>
    exact .ite (HasSimpType_implies_HasTypeA hc) (HasSimpType_implies_HasTypeA ht)
      (HasSimpType_implies_HasTypeA hee)
  | .eq e1 e2 _ hbase he1 he2 =>
    exact .eq (HasSimpType_implies_HasTypeA he1) (HasSimpType_implies_HasTypeA he2)
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    exact .quant (HasSimpType_implies_HasTypeA htr) (HasSimpType_implies_HasTypeA hbody)

/-- An application spine well-typed under `AppSpine` is `HasTypeA`-typed at the arrow type built by
    folding the accumulated argument types over the result type. -/
theorem AppSpine_implies_HasTypeA {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc) := by
  match hspine with
  | .app fn arg aty acc' rty' harg hrest =>
    have h_fn := AppSpine_implies_HasTypeA hrest
    have h_arg := HasSimpType_implies_HasTypeA harg
    exact .app h_fn h_arg
  | .fvar f τ acc' rty' hmem hcollect hbase =>
    have h_eq : τ = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr τ; rw [hcollect] at this; exact this
    exact h_eq ▸ .fvar
  | .op o oty acc' rty' hop hcollect =>
    have h_eq : oty = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr oty; rw [hcollect] at this; exact this
    exact h_eq ▸ .op
  | .fnOp o oty acc' rty' hmem hnpre hcollect hbase =>
    have h_eq : oty = List.foldr LMonoTy.arrow rty' acc' := by
      have := collectArrowTy_foldr oty; rw [hcollect] at this; exact this
    exact h_eq ▸ .op
termination_by structural hspine
end

/-- **Member-denotations of a "distinct" group.** Given the group's common-type witness `hty` (from a WF
    bundle — `∃ τ` base with every member typed at `τ`), the list of each member's `simpDenote` value at
    that common type `hty.choose`. `es.attach` carries each member's `∈ es` proof, which is what lets the
    per-member typing be pulled out of `hty` to gate `simpDenote`. Consumers assert this list is `Nodup`
    ("all members denote to distinct values"). -/
noncomputable def distinctDenote (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {Φ : FVarCtx} {Ψ : FnCtx} (es : List Expression.Expr)
    (hty : ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ) :
    List (Lambda.TyDenote simpTcInterp simpTyVarVal hty.choose) :=
  es.attach.map fun x =>
    simpDenote opInterp fvarVal .nil x.1 hty.choose
      (HasSimpType_implies_HasTypeA (hty.choose_spec.2 x.1 x.2))

/-! ## Op-interpretation consistency — the `opInterp` image of each predefined operator
(classified on the demangled base name) is pinned to its mathematical function.
Part of the source-language denotation model; consumed by `Valid` in the language files.
-/

structure OpInterpConsistent (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) : Prop where
  neg : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Neg⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "int" []])
        = (fun x : Int => -x)
  not : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .bool .Not →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []])
        = (fun x : Bool => !x)
  add : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Add⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x + y)
  sub : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Sub⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x - y)
  mul : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Mul⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => x * y)
  div : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Div⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => if y = 0 then divByZero x else x / y)
  mod_ : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Mod⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]])
        = (fun x y : Int => if y = 0 then modByZero x else x % y)
  lt : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Lt⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x < y))
  le : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Le⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x ≤ y))
  gt : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Gt⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x > y))
  ge : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .numeric ⟨.int, .Ge⟩ →
        opInterp name (.tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]])
        = (fun x y : Int => decide (x ≥ y))
  and_ : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .bool .And →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => x && y)
  or_ : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .bool .Or →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => x || y)
  implies : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .bool .Implies →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => !x || y)
  equiv : ∀ name, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .bool .Equiv →
        opInterp name (.tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]])
        = (fun x y : Bool => decide (x = y))

end Core.Refactor
