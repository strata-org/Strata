/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
# Typed SMT Term semantics

The SMT type checker (`Term.typeCheck`) and the dependently-typed denotational
semantics (`Term.denoteTyped`) for the type checking fragment: a total,
type-indexed denotation gated on a `Term.typeCheck` proof.

## Covered fragment

`Term.typeCheck` accepts (and `Term.denoteTyped` interprets) the following fragment
of SMT-LIB:
* Core theory: `not`, `and`, `or`, `implies`, `eq`, `ite`, `distinct`, and
  uninterpreted functions (`uf`).
* Integer arithmetic (`Ints`): `neg`, `add`, `sub`, `mul`, `div`, `mod`, and the
  comparisons `le`/`lt`/`ge`/`gt`.
* Arrays (`select`/`store`), option literals (`none`/`some`), and quantifiers
  (`forall`/`exist`).
* Denotable base sorts: `Bool`, `Int`, `String`, `BitVec n` — usable through the
  generic operators above.

## Outside this typed fragment (rejected by `Term.typeCheck`)

Note these are omissions of *this* typed fragment, not of Strata's SMT support in general:
the existing `denoteTerm` semantics (`Strata.DL.SMT.Denote`) interprets several of them — in
particular the full bit-vector theory. They are simply not (yet) part of `typeCheck`/`denoteTyped`.

* Reals and real-only operators (`rdiv`, `abs`).
* Bit-vector *operations* (`bvadd`, `bvult`, …) — supported by `denoteTerm`, but here only the
  `BitVec n` base sort (literals) is in scope, not the bit-vector operators. Likewise string/regex
  operations and datatype operators (constructor/tester/selector).
* Sort constructors other than `Array` and user-declared sorts (e.g. `Seq`, `Set`).

Basic properties live in `Strata.DL.SMT.DenoteTypedProps`; the bridge to the
`Option`-partial `denoteTerm` semantics (`Strata.DL.SMT.Denote`) lives in
`Strata.DL.SMT.DenoteSemanticsEquiv`.
-/

module
public import Strata.DL.SMT.Term
import all Strata.DL.SMT.Term
public import Strata.DL.SMT.SmtArray
public import Strata.Util.HList
import all Strata.Util.HList

namespace Strata.SMT.DenoteTyped

/- ═══════════════════════════════════════════════════════════════════════════
   Sort well-formedness
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Typing contexts: declared sort constructors, functions, and variables. -/
abbrev USCtx := List Strata.DL.SMT.Sort
abbrev UFCtx := List UF
abbrev TermVarCtx := List TermVar

/-- Bundled typing context; fields mirror `Strata.DL.SMT.Denote.USContext` / `.UFContext` / `.TermVarContext`. -/
structure TypedContext where
  uss : USCtx
  ufs : UFCtx
  Γ : TermVarCtx

/-- Whether a `TermType` is a denotable primitive base sort — `bool`/`int`/`string`/`bitvec`.
    `real`/`regex` and the compound sorts are excluded for now. -/
def TermType.isBase : TermType → Bool
  | .prim .bool | .prim .int | .prim .string | .prim (.bitvec _) => true
  | _ => false

mutual
/-- Well-formedness of `TermType` w.r.t. `USCtx`. A primitive sort is well-formed only when it is a
    denotable base sort (`isBase`), so `real`/`regex` cannot enter the type-checked fragment
    through the `option`/`array`/variable/UF sort positions — matching their rejection as primitive
    literals. -/
def TermType.WFSort (uss : USCtx) : TermType → Bool
  | .prim p => TermType.isBase (.prim p)
  | .option ty => TermType.WFSort uss ty
  -- Only the built-in `Array` (arity 2) and user-declared sorts (`uss`, matched on name + arity) are
  -- recognized. Other built-in theory sort constructors (e.g. `Seq` arity 1, `Set` arity 1) are not
  -- modeled by the denotation, so they are intentionally not accepted here.
  | .constr id args =>
    ((id == "Array" && args.length == 2)
      || uss.any (fun s => s.name == id && s.arity == args.length))
    && TermType.WFSorts uss args
def TermType.WFSorts (uss : USCtx) : List TermType → Bool
  | [] => true
  | ty :: tys => TermType.WFSort uss ty && TermType.WFSorts uss tys
end

/- ═══════════════════════════════════════════════════════════════════════════
   SMT-term type checker
   ═══════════════════════════════════════════════════════════════════════════ -/

mutual
/-- Type-check a term against a UF context and a variable context, additionally certifying
    that every sort the term mentions is well-formed against a sort context. Returns the term's type
    on success (`.ok`) or a diagnostic message on failure (`.error`). -/
def Term.typeCheck (ctx : TypedContext) : Term → Except String TermType
  -- A primitive literal type-checks only at a denotable base sort.
  | .prim p => if TermType.isBase p.typeOf then .ok p.typeOf
    else .error "primitive literal has a non-denotable base sort"
  -- A variable must match its innermost same-named binder exactly, and its sort must be declared.
  | .var v =>
    if ctx.Γ.find? (fun w => w.id == v.id) = some v ∧ TermType.WFSort ctx.uss v.ty then .ok v.ty
    else .error "variable does not match its innermost same-named binder, or its sort is not well-formed"
  -- A UF application requires its symbol name not be shadowed by an enclosing bound
  -- variable (SMT-LIB lexical scoping), and its signature sorts to be declared.
  | .app (.core (.uf uf)) args rty =>
    if uf ∈ ctx.ufs ∧ uf.id ∉ ctx.Γ.map (·.id) then
      if rty == uf.out && typeCheckArgs ctx args uf.args
          && uf.args.all (TermType.WFSort ctx.uss) && TermType.WFSort ctx.uss uf.out
      then .ok uf.out
      else .error "UF application: return type or arguments do not match the declared signature, or a signature sort is not well-formed"
    else .error "uninterpreted function is not declared, or its symbol is shadowed by a bound variable"
  | .app (.core .not) [t] rty => do
    let tTy ← typeCheck ctx t
    if tTy == .bool && rty == .bool then .ok .bool else .error "'not' expects one Bool operand and a Bool result"
  | .app (.core .and) [t1, t2] rty | .app (.core .or) [t1, t2] rty
  | .app (.core .implies) [t1, t2] rty => do
    let ty1 ← typeCheck ctx t1
    let ty2 ← typeCheck ctx t2
    if ty1 == .bool && ty2 == .bool && rty == .bool then .ok .bool
    else .error "binary Boolean connective expects two Bool operands and a Bool result"
  | .app (.core .eq) [t1, t2] rty => do
    let ty1 ← typeCheck ctx t1
    let ty2 ← typeCheck ctx t2
    if ty1 == ty2 && rty == .bool then .ok .bool
    else .error "'eq' expects two operands of the same type and a Bool result"
  | .app (.core .ite) [c, t, e] rty => do
    let cTy ← typeCheck ctx c
    let tTy ← typeCheck ctx t
    let eTy ← typeCheck ctx e
    if cTy == .bool && tTy == eTy && rty == tTy then .ok tTy
    else .error "'ite' expects a Bool condition, matching branch types, and a matching result type"
  | .app (.num .neg) [t] rty => do
    let tTy ← typeCheck ctx t
    if tTy == .int && rty == .int then .ok .int else .error "integer negation expects an Int operand and an Int result"
  | .app (.num .add) [t1, t2] rty | .app (.num .sub) [t1, t2] rty
  | .app (.num .mul) [t1, t2] rty | .app (.num .div) [t1, t2] rty
  | .app (.num .mod) [t1, t2] rty => do
    let ty1 ← typeCheck ctx t1
    let ty2 ← typeCheck ctx t2
    if ty1 == .int && ty2 == .int && rty == .int then .ok .int
    else .error "binary integer operation expects two Int operands and an Int result"
  | .app (.num .le) [t1, t2] rty | .app (.num .lt) [t1, t2] rty
  | .app (.num .ge) [t1, t2] rty | .app (.num .gt) [t1, t2] rty => do
    let ty1 ← typeCheck ctx t1
    let ty2 ← typeCheck ctx t2
    if ty1 == .int && ty2 == .int && rty == .bool then .ok .bool
    else .error "integer comparison expects two Int operands and a Bool result"
  -- `distinct` is variadic with at least two arguments (per SMT-LIB), all sharing
  -- the first argument's type.
  | .app (.core .distinct) (t1 :: t2 :: ts) rty => do
    let ty ← typeCheck ctx t1
    if typeCheckArgs ctx (t2 :: ts) (List.replicate (t2 :: ts).length ty) && rty == .bool
    then .ok .bool else .error "'distinct' expects at least two operands of a common type and a Bool result"
  -- Push the binder group onto `Γ` reversed. `Γ` is innermost-first and `.var` lookup uses `find?`
  -- (first match wins), so `vs.reverse` makes the LAST-listed binder the innermost — i.e. it shadows
  -- earlier same-name binders in the same group, matching the nested reading `∀ v1, ∀ v2, …` where `v2`
  -- is innermost. (With distinct binder names, order is immaterial.) The trigger is a solver hint (never
  -- denoted); `wfTriggers` type-checks its patterns so their sorts are covered too.
  | .quant _ vs tr body => do
    let bodyTy ← typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body
    if bodyTy == .bool && vs.all (fun v => TermType.WFSort ctx.uss v.ty)
        && Term.wfTriggers { ctx with Γ := vs.reverse ++ ctx.Γ } tr
    then .ok .bool
    else .error "quantifier body must type-check at Bool, and all bound-variable sorts and trigger patterns must be well-formed"
  -- Option literals.
  | .none ty => if TermType.WFSort ctx.uss ty then .ok (.option ty)
    else .error "option 'none' sort is not well-formed"
  | .some t => do
    let τ ← typeCheck ctx t
    .ok (.option τ)
  -- Array theory: `select a i` reads at an index, `store a i e` updates.
  | .app .select [a, i] rty => do
    let aTy ← typeCheck ctx a
    match aTy with
    | .constr "Array" [k, v] =>
      let iTy ← typeCheck ctx i
      if iTy == k && rty == v then .ok v
      else .error "array 'select': index sort must match the array's key sort and the result must match the value sort"
    | _ => .error "array 'select' expects its first argument to be an Array"
  | .app .store [a, i, e] rty => do
    let aTy ← typeCheck ctx a
    match aTy with
    | .constr "Array" [k, v] =>
      let iTy ← typeCheck ctx i
      let eTy ← typeCheck ctx e
      if iTy == k && eTy == v && rty == .constr "Array" [k, v]
      then .ok (.constr "Array" [k, v])
      else .error "array 'store': index/element sorts must match the array's key/value sorts and the result must be the array type"
    | _ => .error "array 'store' expects its first argument to be an Array"
  | _ => .error "unsupported or malformed term"

def Term.typeCheckArgs (ctx : TypedContext) :
    List Term → List TermType → Bool
  | [], [] => true
  | t :: ts, expectedTy :: rest =>
    match typeCheck ctx t with
    | .ok ty => ty == expectedTy && typeCheckArgs ctx ts rest
    | .error _ => false
  | _, _ => false

/-- Every term in the list type-checks to some type (used to type-check quantifier trigger patterns,
    whose types are irrelevant). -/
def Term.typeCheckAll (ctx : TypedContext) : List Term → Bool
  | [] => true
  | t :: ts => (typeCheck ctx t).toOption.isSome && typeCheckAll ctx ts

/-- Well-formedness of a quantifier's triggers: every pattern in every group must type-check (to some
    type). An empty trigger list (no patterns) is trivially well-formed. -/
def Term.wfTriggers (ctx : TypedContext) : List (List Term) → Bool
  | [] => true
  | group :: rest => typeCheckAll ctx group && wfTriggers ctx rest
end

/- ═══════════════════════════════════════════════════════════════════════════
   Typed Term denotation
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Interpretation of the non-primitive sorts: assigns each sort constructor `TermType.constr id args`
    a Lean carrier. -/
def SortInterp := String → List TermType → Type

/-- Every carrier a `SortInterp` produces is inhabited. -/
class SortInterp.AllInhabited (σ : SortInterp) : Type where
  inhabited : ∀ id args, Inhabited (σ id args)

/-- An interpretation of the SMT `Array` sort: a carrier `Arr` with `select`/`store`/`const` satisfying
    the SMT-LIB `ArraysEx` axioms, including extensionality. `TermType.denoteTyped`/`Term.denoteTyped`
    are parameterized over it, so the same semantics can be instantiated at different array carriers. -/
structure ArrayTheory where
  Arr : Type → Type → Type
  select : {α β : Type} → Arr α β → α → β
  store : {α β : Type} → Arr α β → α → β → Arr α β
  const : {α β : Type} → β → Arr α β
  select_store_self : ∀ {α β : Type} (a : Arr α β) (i : α) (v : β), select (store a i v) i = v
  select_store_of_ne : ∀ {α β : Type} (a : Arr α β) (i j : α) (v : β),
    j ≠ i → select (store a i v) j = select a j
  select_const : ∀ {α β : Type} (v : β) (i : α), select (const v : Arr α β) i = v
  ext : ∀ {α β : Type} (a b : Arr α β), (∀ i, select a i = select b i) → a = b

/-- The concrete `SmtArray` model as an `ArrayTheory` instance. -/
noncomputable def SmtArrayTheory : ArrayTheory where
  Arr := fun α β => SmtArray α β
  select := fun a i => a.select i
  store := fun a i v => @SmtArray.store _ _ (Classical.typeDecidableEq _) a i v
  const := fun v => SmtArray.const v
  select_store_self := fun a i v => @SmtArray.select_store_self _ _ (Classical.typeDecidableEq _) a i v
  select_store_of_ne := fun a i j v hji =>
    @SmtArray.select_store_of_ne _ _ (Classical.typeDecidableEq _) a i j v hji
  select_const := fun v i => SmtArray.select_const v i
  ext := fun a b h => SmtArray.ext a b h

/-- Denotation of SMT types: the `Array` constructor is interpreted by the array theory `𝒜`; every other
    constructor gets its carrier from `σ`. -/
@[reducible] def TermType.denoteTyped (σ : SortInterp) (𝒜 : ArrayTheory) : TermType → Type
  | .prim .bool => Bool
  | .prim .int => Int
  | .prim (.bitvec n) => BitVec n
  | .prim .string => String
  | .option ty => Option (TermType.denoteTyped σ 𝒜 ty)
  | .constr "Array" [k, v] => 𝒜.Arr (TermType.denoteTyped σ 𝒜 k) (TermType.denoteTyped σ 𝒜 v)
  | .constr id args => σ id args
  | _ => Unit


/-- Curried function type for denotation.
    `UF.denoteTyped [.int, .bool] .int = Int → Bool → Int` -/
def UF.denoteTyped' (σ : SortInterp) (𝒜 : ArrayTheory) : List TermType → TermType → Type
  | [], out => TermType.denoteTyped σ 𝒜 out
  | arg :: rest, out => TermType.denoteTyped σ 𝒜 arg → UF.denoteTyped' σ 𝒜 rest out

def UF.denoteTyped (σ : SortInterp) (𝒜 : ArrayTheory) (uf : UF) : Type :=
  UF.denoteTyped' σ 𝒜 uf.args uf.out

/-- Apply a curried UF denotation to an HList of argument values. -/
noncomputable def UF.applyDenoteTyped' (σ : SortInterp) (𝒜 : ArrayTheory) :
    (argTys : List TermType) → (out : TermType) →
    UF.denoteTyped' σ 𝒜 argTys out → HList (TermType.denoteTyped σ 𝒜) argTys →
    TermType.denoteTyped σ 𝒜 out
  | [], _, val, .nil => val
  | _ :: rest, out, f, .cons v vs => UF.applyDenoteTyped' σ 𝒜 rest out (f v) vs

noncomputable def UF.applyDenoteTyped (σ : SortInterp) (𝒜 : ArrayTheory) (uf : UF) :
    UF.denoteTyped σ 𝒜 uf → HList (TermType.denoteTyped σ 𝒜) uf.args → TermType.denoteTyped σ 𝒜 uf.out :=
  UF.applyDenoteTyped' σ 𝒜 uf.args uf.out

/-- UF interpretation: maps each UF signature to a curried
    function from argument types to output type. -/
def UFInterp (σ : SortInterp) (𝒜 : ArrayTheory) := (uf : UF) → UF.denoteTyped σ 𝒜 uf

/-- SMT variable environment: maps variables to values of their types. -/
def VarEnv (σ : SortInterp) (𝒜 : ArrayTheory) := (x : TermVar) → (TermType.denoteTyped σ 𝒜 x.ty)


/- ═══════════════════════════════════════════════════════════════════════════
   Type-checking inversion lemmas (consumed by `Term.denoteTyped`)
   ═══════════════════════════════════════════════════════════════════════════ -/

private def Term.typeCheck_prim_inv {ctx : TypedContext} {p : TermPrim} {τ : TermType}
    (h : Term.typeCheck ctx (.prim p) = .ok τ) : τ = p.typeOf := by
  simp only [Term.typeCheck] at h
  split at h <;> simp_all

private def Term.typeCheck_var_inv {ctx : TypedContext} {v : TermVar} {τ : TermType}
    (h : Term.typeCheck ctx (.var v) = .ok τ) :
    ctx.Γ.find? (fun w => w.id == v.id) = some v ∧ v.ty = τ := by
  simp only [Term.typeCheck] at h
  split at h <;> simp_all

private def Term.typeCheck_not_inv {ctx : TypedContext} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core .not) [t] rty) = .ok τ) :
    Term.typeCheck ctx t = .ok .bool ∧ τ = .bool := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h <;> (try split at h) <;> simp_all

private def Term.typeCheck_boolBin_inv {ctx : TypedContext} {op : Op.Core}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core op) [t1, t2] rty) = .ok τ)
    (hop : op = .and ∨ op = .or ∨ op = .implies) :
    Term.typeCheck ctx t1 = .ok .bool ∧ Term.typeCheck ctx t2 = .ok .bool ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl <;>
    (simp only [Term.typeCheck, bind, Except.bind] at h
     split at h <;> (try split at h) <;> (try split at h) <;> simp_all)

private def Term.typeCheck_eq_inv {ctx : TypedContext} {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core .eq) [t1, t2] rty) = .ok τ) :
    Σ' τ', Term.typeCheck ctx t1 = .ok τ' ∧ Term.typeCheck ctx t2 = .ok τ' ∧ τ = .bool := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i ty1 heq1
    split at h
    · simp at h
    · rename_i ty2 heq2
      split at h
      · exact ⟨ty1, heq1, by simp_all, by simp_all⟩
      · simp at h

private def Term.typeCheck_ite_inv {ctx : TypedContext} {c t e : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core .ite) [c, t, e] rty) = .ok τ) :
    Term.typeCheck ctx c = .ok .bool ∧ Term.typeCheck ctx t = .ok τ ∧
    Term.typeCheck ctx e = .ok τ := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all

private def Term.typeCheck_intUn_inv {ctx : TypedContext} {t : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.num .neg) [t] rty) = .ok τ) :
    Term.typeCheck ctx t = .ok .int ∧ τ = .int := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h <;> (try split at h) <;> simp_all

private def Term.typeCheck_intBin_inv {ctx : TypedContext} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.num op) [t1, t2] rty) = .ok τ)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod) :
    Term.typeCheck ctx t1 = .ok .int ∧ Term.typeCheck ctx t2 = .ok .int ∧ τ = .int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Term.typeCheck, bind, Except.bind] at h
     split at h <;> (try split at h) <;> (try split at h) <;> simp_all)

private def Term.typeCheck_intCmp_inv {ctx : TypedContext} {op : Op.Num}
    {t1 t2 : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.num op) [t1, t2] rty) = .ok τ)
    (hop : op = .le ∨ op = .lt ∨ op = .ge ∨ op = .gt) :
    Term.typeCheck ctx t1 = .ok .int ∧ Term.typeCheck ctx t2 = .ok .int ∧ τ = .bool := by
  rcases hop with rfl | rfl | rfl | rfl <;>
    (simp only [Term.typeCheck, bind, Except.bind] at h
     split at h <;> (try split at h) <;> (try split at h) <;> simp_all)

/-- Inversion for a well-typed quantifier: when `.quant k vs tr body` type-checks to `τ`, the body
    type-checks to `.bool` in the binder-extended context (`vs.reverse ++ ctx.Γ`), and the overall
    result type is `.bool`. The bound-sort well-formedness and trigger-well-formedness guards inside
    `Term.typeCheck`'s `.quant` case are elided; only the body/return facts survive. -/
private def Term.typeCheck_quant_inv {ctx : TypedContext} {tr : List (List Term)}
    {k : Strata.SMT.QuantifierKind} {vs : List TermVar} {body : Term} {τ : TermType}
    (h : Term.typeCheck ctx (.quant k vs tr body) = .ok τ) :
    Term.typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body = .ok .bool ∧ τ = .bool := by
  -- Invert the body-bind; the guard's `vs.all`/`wfTriggers` conjuncts don't affect the body/return facts.
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h <;> (try split at h) <;> simp_all

/-- Inversion for `distinct` on an argument list of length ≥ 2: recovers the
    shared element type `ty` and the fact that the tail type-checks homogeneously. -/
private def Term.typeCheck_distinct_inv {ctx : TypedContext} {t1 t2 : Term} {ts : List Term}
    {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core .distinct) (t1 :: t2 :: ts) rty) = .ok τ) :
    Σ' ty, Term.typeCheck ctx t1 = .ok ty ∧
      Term.typeCheckArgs ctx (t2 :: ts) (List.replicate (t2 :: ts).length ty) = true ∧
      τ = .bool := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i ty heq
    split at h
    · exact ⟨ty, heq, by simp_all, by simp_all⟩
    · simp at h

private def Term.typeCheck_none_inv {ctx : TypedContext} {ty τ : TermType}
    (h : Term.typeCheck ctx (.none ty) = .ok τ) : τ = .option ty := by
  simp only [Term.typeCheck] at h
  split at h <;> simp_all

private def Term.typeCheck_some_inv {ctx : TypedContext} {t : Term} {τ : TermType}
    (h : Term.typeCheck ctx (.some t) = .ok τ) :
    Σ' τ', Term.typeCheck ctx t = .ok τ' ∧ τ = .option τ' := by
  simp only [Term.typeCheck, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i τ' heq
    simp only [Except.ok.injEq] at h
    exact ⟨τ', heq, h.symm⟩

private def Term.typeCheck_select_inv {ctx : TypedContext} {a i : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app .select [a, i] rty) = .ok τ) :
    Σ' k v, Term.typeCheck ctx a = .ok (.constr "Array" [k, v]) ∧
      Term.typeCheck ctx i = .ok k ∧ rty = v ∧ τ = v := by
  simp only [Term.typeCheck] at h; revert h
  cases ha : Term.typeCheck ctx a with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok aTy =>
    simp only [bind, Except.bind]; intro h
    split at h
    · rename_i k v
      revert h
      cases hi : Term.typeCheck ctx i with
      | error e => intro h; simp at h
      | ok iTy =>
        simp only []; intro h
        split at h
        · refine ⟨k, v, ?_, ?_, ?_, ?_⟩ <;> simp_all
        · simp at h
    · simp at h

private def Term.typeCheck_store_inv {ctx : TypedContext} {a i e : Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app .store [a, i, e] rty) = .ok τ) :
    Σ' k v, Term.typeCheck ctx a = .ok (.constr "Array" [k, v]) ∧
      Term.typeCheck ctx i = .ok k ∧ Term.typeCheck ctx e = .ok v ∧
      rty = .constr "Array" [k, v] ∧ τ = .constr "Array" [k, v] := by
  simp only [Term.typeCheck] at h; revert h
  cases ha : Term.typeCheck ctx a with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok aTy =>
    simp only [bind, Except.bind]; intro h
    split at h
    · rename_i k v
      revert h
      cases hi : Term.typeCheck ctx i with
      | error e => intro h; simp at h
      | ok iTy =>
        cases he : Term.typeCheck ctx e with
        | error e => intro h; simp at h
        | ok eTy =>
          simp only []; intro h
          split at h
          · refine ⟨k, v, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
          · simp at h
    · simp at h

/-- Flatten a homogeneous `HList` into a plain list. -/
def hlistReplicateToList {α : Type} {f : α → Type} {a : α} :
    (n : Nat) → HList f (List.replicate n a) → List (f a)
  | 0, _ => []
  | _ + 1, .cons x xs => x :: hlistReplicateToList _ xs


mutual
/-- Total denotation of a type-checked SMT term into a Lean value of the corresponding type. -/
noncomputable def Term.denoteTyped
    {ctx : TypedContext}
    {σ : SortInterp} {𝒜 : ArrayTheory}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (tm : Term) (τ : TermType)
    (h : Term.typeCheck ctx tm = .ok τ)
    : TermType.denoteTyped σ 𝒜 τ :=
  match tm with
  | .prim p =>
    have heq := Term.typeCheck_prim_inv h
    heq ▸ (match p with
      | .bool b => (b : TermType.denoteTyped σ 𝒜 (TermPrim.bool b).typeOf)
      | .int i => (i : TermType.denoteTyped σ 𝒜 (TermPrim.int i).typeOf)
      | .string s => (s : TermType.denoteTyped σ 𝒜 (TermPrim.string s).typeOf)
      | .bitvec b => (b : TermType.denoteTyped σ 𝒜 (TermPrim.bitvec b).typeOf)
      | .real _ => ())
  | .var v =>
    let ⟨_, heq⟩ := Term.typeCheck_var_inv h
    cast (by rw [← heq]) (env v)
  | .app (.core (.uf uf)) args _ =>
    have hargs : Term.typeCheckArgs ctx args uf.args = true := by
      simp only [Term.typeCheck] at h; split at h <;> (try split at h) <;> simp_all
    have hout : τ = uf.out := by
      simp only [Term.typeCheck] at h; split at h <;> (try split at h) <;> simp_all
    let argVals := Term.denoteTypedArgs ufInterp env divByZero modByZero args uf.args hargs
    cast (by rw [hout]) (UF.applyDenoteTyped' σ 𝒜 uf.args uf.out (ufInterp uf) argVals)
  | .app (.core .not) [t] _ =>
    let ⟨ht, heq⟩ := Term.typeCheck_not_inv h
    cast (by rw [heq]) (!(Term.denoteTyped ufInterp env divByZero modByZero t .bool ht))
  | .app (.core .and) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inl rfl)
    cast (by rw [heq]) ((Term.denoteTyped ufInterp env divByZero modByZero t1 .bool h1) && (Term.denoteTyped ufInterp env divByZero modByZero t2 .bool h2))
  | .app (.core .or) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((Term.denoteTyped ufInterp env divByZero modByZero t1 .bool h1) || (Term.denoteTyped ufInterp env divByZero modByZero t2 .bool h2))
  | .app (.core .implies) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inr rfl))
    cast (by rw [heq]) (!(Term.denoteTyped ufInterp env divByZero modByZero t1 .bool h1) || (Term.denoteTyped ufInterp env divByZero modByZero t2 .bool h2))
  | .app (.core .eq) [t1, t2] _ =>
    let ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv h
    cast (by rw [heq]) (@decide (Term.denoteTyped ufInterp env divByZero modByZero t1 τ' h1 = Term.denoteTyped ufInterp env divByZero modByZero t2 τ' h2)
      (Classical.propDecidable _))
  | .app (.core .ite) [c, t, e] _ =>
    let ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv h
    bif Term.denoteTyped ufInterp env divByZero modByZero c .bool hc then Term.denoteTyped ufInterp env divByZero modByZero t τ ht
    else Term.denoteTyped ufInterp env divByZero modByZero e τ he
  | .app (.num .neg) [t] _ =>
    let ⟨ht, heq⟩ := Term.typeCheck_intUn_inv h
    cast (by rw [heq]) (-(Term.denoteTyped ufInterp env divByZero modByZero t .int ht))
  | .app (.num .add) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inl rfl)
    cast (by rw [heq]) ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) + (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2))
  | .app (.num .sub) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inl rfl))
    cast (by rw [heq]) ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) - (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2))
  | .app (.num .mul) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) * (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2))
  | .app (.num .div) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inl rfl))))
    cast (by rw [heq])
      (let v1 := Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1
       let v2 := Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2
       if v2 = 0 then divByZero v1 else v1 / v2)
  | .app (.num .mod) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inr rfl))))
    cast (by rw [heq])
      (let v1 := Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1
       let v2 := Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2
       if v2 = 0 then modByZero v1 else v1 % v2)
  | .app (.num .le) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inl rfl)
    cast (by rw [heq]) (decide ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) ≤ (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2)))
  | .app (.num .lt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inl rfl))
    cast (by rw [heq]) (decide ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) < (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2)))
  | .app (.num .ge) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inl rfl)))
    cast (by rw [heq]) (decide ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) ≥ (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2)))
  | .app (.num .gt) [t1, t2] _ =>
    let ⟨h1, h2, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inr rfl)))
    cast (by rw [heq]) (decide ((Term.denoteTyped ufInterp env divByZero modByZero t1 .int h1) > (Term.denoteTyped ufInterp env divByZero modByZero t2 .int h2)))
  | .quant k vs tr body =>
    let ⟨hbody, heq⟩ := Term.typeCheck_quant_inv h
    let combinedEnv (ext : VarEnv σ 𝒜) : VarEnv σ 𝒜 :=
      fun v =>
        if hv : v ∈ vs then ext v
        else env v
    cast (by rw [heq]) (@decide
      (match k with
       | .all => ∀ (ext : VarEnv σ 𝒜), Term.denoteTyped ufInterp (combinedEnv ext) divByZero modByZero body .bool hbody = true
       | .exist => ∃ (ext : VarEnv σ 𝒜), Term.denoteTyped ufInterp (combinedEnv ext) divByZero modByZero body .bool hbody = true)
      (Classical.propDecidable _))
  | .app (.core .distinct) (t1 :: t2 :: ts) _ =>
    -- All args share `ty`; decide pairwise distinctness of their denotations.
    let ⟨ty, ht, hts, heq⟩ := Term.typeCheck_distinct_inv h
    let args := t1 :: t2 :: ts
    let hargs : Term.typeCheckArgs ctx args (List.replicate args.length ty) = true := by
      show Term.typeCheckArgs ctx (t1 :: t2 :: ts)
        (ty :: List.replicate (t2 :: ts).length ty) = true
      simp only [Term.typeCheckArgs, ht, BEq.beq, decide_eq_true_eq, hts, Bool.and_true]
    let argVals := Term.denoteTypedArgs ufInterp env divByZero modByZero args (List.replicate args.length ty) hargs
    cast (by rw [heq]) (@decide
      ((hlistReplicateToList args.length argVals).Pairwise (· ≠ ·))
      (Classical.propDecidable _))
  | .app (.core .distinct) [] _ | .app (.core .distinct) [_] _ =>
    False.elim (by unfold Term.typeCheck at h; exact absurd h nofun)
  | .none ty =>
    have heq := Term.typeCheck_none_inv h
    cast (by rw [heq]) (none : TermType.denoteTyped σ 𝒜 (.option ty))
  | .some t =>
    let ⟨τ', ht, heq⟩ := Term.typeCheck_some_inv h
    cast (by rw [heq])
      (some (Term.denoteTyped ufInterp env divByZero modByZero t τ' ht) :
        TermType.denoteTyped σ 𝒜 (.option τ'))
  | .app .select [a, i] _ =>
    let ⟨k, v, ha, hi, _, heq⟩ := Term.typeCheck_select_inv h
    cast (by rw [heq])
      (𝒜.select
        (Term.denoteTyped ufInterp env divByZero modByZero a (.constr "Array" [k, v]) ha)
        (Term.denoteTyped ufInterp env divByZero modByZero i k hi))
  | .app .store [a, i, e] _ =>
    let ⟨k, v, ha, hi, he, _, heq⟩ := Term.typeCheck_store_inv h
    cast (by rw [heq]; rfl)
      (𝒜.store
        (Term.denoteTyped ufInterp env divByZero modByZero a (.constr "Array" [k, v]) ha)
        (Term.denoteTyped ufInterp env divByZero modByZero i k hi)
        (Term.denoteTyped ufInterp env divByZero modByZero e v he))

/-- Denote a list of type-checked arguments, producing an HList of values. -/
noncomputable def Term.denoteTypedArgs {σ : SortInterp} {𝒜 : ArrayTheory}
    {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (args : List Term) (argTys : List TermType)
    (htc : Term.typeCheckArgs ctx args argTys = true)
    : HList (TermType.denoteTyped σ 𝒜) argTys :=
  match args, argTys, htc with
  | [], [], _ => .nil
  | t :: ts, ty :: tys, htc =>
    have htc_hd : Term.typeCheck ctx t = .ok ty := by
      simp only [Term.typeCheckArgs] at htc
      split at htc <;> simp_all [BEq.beq, decide_eq_true_eq]
    have htc_rest : Term.typeCheckArgs ctx ts tys = true := by
      simp only [Term.typeCheckArgs] at htc
      split at htc <;> simp_all [BEq.beq]
    .cons (Term.denoteTyped ufInterp env divByZero modByZero t ty htc_hd)
          (Term.denoteTypedArgs ufInterp env divByZero modByZero ts tys htc_rest)
end

end Strata.SMT.DenoteTyped
