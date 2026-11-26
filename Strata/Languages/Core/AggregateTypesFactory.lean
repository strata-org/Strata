/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public meta import Strata.Languages.Core.Identifiers
public import Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import Strata.DL.Lambda.LExprProps

/-! # Core's factory functions over aggregate types

The functions of `Core.Factory` over `Map`, `Set` and `Sequence`, which are all polymorphic in
the types of their keys, values or elements. `Core.Factory` collects them with the others.

- `mapTy`, `seqTy`, `setTy` — the aggregate types.
- `polyLitOp` — the combinator for a polymorphic function whose concrete evaluator computes on
  literals; the `Map` and `Sequence` operations use it, with the evaluators in `AggregateLitEval`.
- `litToOpExpr` — a collection literal as the operator expression that builds it.
- The `Map` operations (`mapConstFunc`, `mapSelectFunc`, `mapUpdateFunc`), the `Set`
  operations (`setEmptyFunc`, `setContainsFunc`, ...) and the `Sequence` operations
  (`seqLengthFunc`, `seqEmptyFunc`, ...).
-/

namespace Core
open Lambda LTy.Syntax LExpr.SyntaxMono Core.Syntax
open Strata.DL.Util (FuncPrecondition)

public section

/-! ## Aggregate types -/

/-- A total map from `keyTy` to `valTy`. Extensional only under the array encoding
    (see `VerifyOptions.useArrayTheory`): with `useArrayTheory := false`, two maps
    equal at every key are not provably equal. -/
@[expose, match_pattern]
def mapTy (keyTy : LMonoTy) (valTy : LMonoTy) : LMonoTy :=
  .tcons "Map" [keyTy, valTy]

@[expose, match_pattern]
def seqTy (elemTy : LMonoTy) : LMonoTy :=
  .tcons "Sequence" [elemTy]

/-- A mathematical (immutable, unordered) set of `elemTy`.

    A distinct sort rather than a `Map elemTy bool` alias: keeping it distinct is what
    lets the SMT encoder later target a dedicated set theory (or a specialized
    axiomatization) without every `Map` paying for it.

    What a proof can conclude about two sets depends on the SMT encoding (see
    `VerifyOptions.useArrayTheory`):
    - With `useArrayTheory := false` (the `Core.verify` default; `gen_smt_vcs` defaults
      to `true`), the encoder declares a fresh sort (named by `smtSortName`, since cvc5
      and z3 already define a sort `Set`), and the `Set.*` operations are declared
      functions constrained by the membership axioms below. This is sound but not
      extensional: for two sets `s` and `t` with the same members, neither `s == t` nor
      `f(s) == f(t)` for a function `f` over sets is provable.
    - With `--use-array-theory`, `Set elemTy` encodes as `Array elemTy bool`.
      `Set.contains`, `Set.insert` and `Set.remove` map to `select` and `store`;
      `Set.empty`, `Set.union`, `Set.intersect` and `Set.difference` stay declared
      functions with their membership axioms. The theory of arrays is extensional, so
      any two sets with the same members, including the results of those functions,
      are equal. -/
@[expose, match_pattern]
def setTy (elemTy : LMonoTy) : LMonoTy :=
  .tcons "Set" [elemTy]

/-! ## Literal combinator

`polyLitOp` builds a well-formed `WFLFunc` whose concrete evaluator computes on
literals: it applies to calls whose arguments are all constants, and returns a
constant. -/

/-- The largest literal, counted in constants (`LConst.size`), that a `polyLitOp` evaluator
    returns. The SMT encoding spells a collection literal out constant by constant, so a large
    one encodes much larger than the operations that built it, whose repeated subterms the
    encoding shares (sequences doubled by appends, for example). Past this size the call is
    left as it is, to the solver and the function's axioms. -/
@[expose] def maxLitSize : Nat := 64

/-- A polymorphic function with a concrete evaluator on literals: on a call whose
    `inputs.length` arguments are all constants, it returns the constant `eval`
    computes from the operator's type annotation and the argument literals, if
    any, provided it is well typed (`LConst.wt`) at the output type of the
    operator's type annotation and has at most `maxLitSize` constants. -/
@[inline]
def polyLitOp (n : CoreLParams.Identifier) (typeArgs : List String)
    (inputs : List (CoreLParams.Identifier × LMonoTy)) (output : LMonoTy)
    (eval : Option LMonoTy → List LConst → Option LConst)
    (axioms : List (LExpr CoreLParams.mono) := [])
    (preconditions :
      List (FuncPrecondition (LExpr CoreLParams.mono) CoreLParams.Metadata) := [])
    (h_nodup : List.Nodup (inputs.map (·.1.name)) := by first | decide | grind)
    (h_ta_nodup : List.Nodup typeArgs := by grind)
    (h_inputs : ∀ ty, ty ∈ ListMap.values inputs →
      ty.freeVars ⊆ typeArgs := by first | decide | grind)
    (h_output : output.freeVars ⊆ typeArgs
      := by first | decide | grind)
    (h_precond : ∀ p, p ∈ preconditions →
      (LExpr.freeVars p.expr).map (·.1.name) ⊆ inputs.map (·.1.name)
      := by first | decide | grind)
    (h_ta_no_gen : ∀ ta, ta ∈ typeArgs → ¬ (genTyPrefix.toList.isPrefixOf ta.toList = true)
      := by first | decide | grind) : WFLFunc CoreLParams :=
  ⟨{ name := n, typeArgs := typeArgs, inputs := inputs, output := output,
     axioms := axioms, preconditions := preconditions,
     concreteEval := some (fun md opTy args =>
       if args.length = inputs.length then
         ((LExpr.constArgs? args).bind (eval opTy)).bind fun r =>
           if r.wt && decide (opTy.map (LMonoTy.arrowResult inputs.length) = some r.ty) &&
               decide (r.size ≤ maxLitSize) then
             some (LExpr.const md r)
           else none
       else none) }, {
    arg_nodup := h_nodup
    concreteEval_argmatch := by
      intro fn md opTy args res hfn heval
      simp only [Option.some.injEq] at hfn; subst hfn
      simp only at heval
      split at heval
      · assumption
      · cases heval
    body_or_concreteEval := by simp
    constr_no_eval := by simp
    typeArgs_nodup := h_ta_nodup
    inputs_typevars_in_typeArgs := h_inputs
    output_typevars_in_typeArgs := h_output
    typeArgs_no_gen_prefix := h_ta_no_gen
    body_freevars := by intro b hb; simp at hb
    precond_freevars := h_precond
    concreteEval_eraseMetadata := by
      intro ceval h md1 md2 opTy args1 args2 res1 hmap heval
      simp only [Option.some.injEq] at h; subst h
      have hlen : args1.length = args2.length := by
        have hl := congrArg List.length hmap; simpa using hl
      have hc := LExpr.constArgs?_eraseMetadata hmap
      simp only at heval ⊢
      split at heval
      · rename_i hl
        rw [ite_eq_left (hlen ▸ hl), ← hc]
        obtain ⟨r, hr, hres⟩ := Option.bind_eq_some_iff.mp heval
        split at hres
        · rename_i hchk
          simp only [Option.some.injEq] at hres; subst hres
          exact ⟨LExpr.const md2 r, by rw [hr]; simp only [Option.bind_some, hchk, ↓reduceIte],
            by simp [LExpr.eraseMetadata, LExpr.replaceMetadata]⟩
        · cases hres
      · cases heval
    concreteEval_freeVars := by
      intro ceval h md opTy args res heval z hz
      simp only [Option.some.injEq] at h; subst h
      simp only at heval
      split at heval
      · obtain ⟨r, _, hres⟩ := Option.bind_eq_some_iff.mp heval
        split at hres
        · simp only [Option.some.injEq] at hres; subst hres
          simp [LExpr.LExpr.getVars] at hz
        · cases hres
      · cases heval
  }⟩

/-! ## Concrete evaluation of `Map` and `Sequence` operations

The `Map` and `Sequence` operations evaluate calls whose arguments are literals
(`LConst.mapConst`, `LConst.sequenceConst` and primitive literals), building
literals. `mapConst` and `Sequence.empty` read the key, value or element sort from
the type annotation of their operator, since their arguments do not determine it.

An evaluator compares keys (`select`, `update`) or elements (`Sequence.contains`)
syntactically, which decides their equality at a sort without `Map` when the key or element
looked up holds no datatype value (`LConst.hasData`), so it declines otherwise. The partial `Sequence`
operations, and their unchecked `!` variants, evaluate only within bounds. -/

namespace AggregateLitEval

/-- `mapConst(d)` at operator type `v → Map k v`: the map literal sending every key
    to `d`. It reads the annotation, so it returns `none` unless the annotation is ground
    (`ConcreteEval`, `mapConstFunc_eval_ground`). Like the other evaluators it leaves typing
    to `polyLitOp`, which rejects the literal unless `d` is well typed at the value sort. -/
@[expose] def mapConst : Option LMonoTy → List LConst → Option LConst
  | some t, [d] =>
    match t.toSort? with
    | some (.tcons "arrow" [_, .tcons "Map" [ks, vs]]) => some (.mapConst ks vs d #[])
    | _ => none
  | _, _ => none

/-- `select(m, key)` on a map literal: the value of `key` (`LConst.mapSelect`). -/
@[expose] def mapSelect : Option LMonoTy → List LConst → Option LConst
  | _, [.mapConst k _ d xs, key] =>
    if !k.hasMap && !key.hasData then some (LConst.mapSelect d xs key) else none
  | _, _ => none

/-- The entries of a map literal after setting key `k` to `v`: `(k, v)` followed by the entries
    whose key is not syntactically `k`, which the new entry shadows. The first entry counts, so
    these entries give the map updated at `k` at every key sort. No entry is dropped for having
    the default value. -/
@[expose] def mapUpdateFront (es : Array (LConst × LConst)) (k v : LConst) :
    Array (LConst × LConst) :=
  #[(k, v)] ++ es.filter (fun e => e.1 != k)

/-- `update(m, key, x)` on a map literal at a key sort without `Map`: `LConst.mapUpdate` when
    `key` holds no datatype value (`LConst.hasData`), and `mapUpdateFront` when it holds one. -/
@[expose] def mapUpdate : Option LMonoTy → List LConst → Option LConst
  | _, [.mapConst k v d xs, key, x] =>
    if k.hasMap then none
    else if !key.hasData then some (.mapConst k v d (LConst.mapUpdate d xs key x))
    else some (.mapConst k v d (mapUpdateFront xs key x))
  | _, _ => none

/-- `Sequence.empty()` at operator type `Sequence a`. It reads the annotation, so it returns
    `none` unless the annotation is ground (`ConcreteEval`, `seqEmptyFunc_eval_ground`). -/
@[expose] def seqEmpty : Option LMonoTy → List LConst → Option LConst
  | some t, [] =>
    match t.toSort? with
    | some (.tcons "Sequence" [a]) => some (.sequenceConst a #[])
    | _ => none
  | _, _ => none

/-- `Sequence.length(s)`. -/
@[expose] def seqLength : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst _ xs] => some (.intConst xs.size)
  | _, _ => none

/-- `Sequence.append(s, t)`. -/
@[expose] def seqAppend : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, .sequenceConst _ xs'] => some (.sequenceConst a (xs ++ xs'))
  | _, _ => none

/-- `Sequence.select(s, i)` (and `Sequence.select!`) for `0 ≤ i < length(s)`. -/
@[expose] def seqSelect : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst _ xs, .intConst i] =>
    if h : 0 ≤ i ∧ i.toNat < xs.size then some xs[i.toNat] else none
  | _, _ => none

/-- `Sequence.build(s, x)`: `s` with `x` appended. -/
@[expose] def seqBuild : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, x] => some (.sequenceConst a (xs.push x))
  | _, _ => none

/-- `Sequence.update(s, i, x)` (and `Sequence.update!`) for `0 ≤ i < length(s)`. -/
@[expose] def seqUpdate : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, .intConst i, x] =>
    if h : 0 ≤ i ∧ i.toNat < xs.size then some (.sequenceConst a (xs.set i.toNat x h.2))
    else none
  | _, _ => none

/-- `Sequence.contains(s, x)`, at an element sort without `Map` and an `x` holding no datatype
    value (`LConst.hasData`). -/
@[expose] def seqContains : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, x] =>
    if !a.hasMap && !x.hasData then some (.boolConst (xs.contains x)) else none
  | _, _ => none

/-- `Sequence.take(s, n)` (and `Sequence.take!`) for `0 ≤ n ≤ length(s)`. -/
@[expose] def seqTake : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, .intConst n] =>
    if 0 ≤ n ∧ n.toNat ≤ xs.size then some (.sequenceConst a (xs.extract 0 n.toNat)) else none
  | _, _ => none

/-- `Sequence.drop(s, n)` (and `Sequence.drop!`) for `0 ≤ n ≤ length(s)`. -/
@[expose] def seqDrop : Option LMonoTy → List LConst → Option LConst
  | _, [.sequenceConst a xs, .intConst n] =>
    if 0 ≤ n ∧ n.toNat ≤ xs.size then some (.sequenceConst a (xs.extract n.toNat xs.size))
    else none
  | _, _ => none

/-- The value at `key` of a map literal with default `d` and entries `es`, as the chain
    `ite(key == k₁, v₁, ite(key == k₂, v₂, … d))` over the entries. An entry whose key is
    syntactically `key` closes the chain with its value. Every node is a constant, an equality of
    two constants, or an `ite` whose condition is such an equality. -/
@[expose] def selectChain (md : CoreExprMetadata) (key d : LConst) :
    List (LConst × LConst) → Expression.Expr
  | [] => .const md d
  | (k, v) :: rest =>
    if k = key then .const md v
    else .ite md (.eq md (.const md key) (.const md k)) (.const md v) (selectChain md key d rest)

/-- `select(m, key)` on a map literal at a key sort without `Map`, for a key holding a datatype
    value (`LConst.hasData`): the chain `selectChain`, when the literal is well typed, `key` is a
    well-typed constant of the key sort, the operator's annotation has the value sort as its
    result type, and the literal has at most `maxLitSize` constants. -/
@[expose] def selectChainEval : ConcreteEval CoreLParams := fun md opTy args =>
  match LExpr.constArgs? args with
  | some [.mapConst k v d ⟨es⟩, key] =>
    if key.hasData && !k.hasMap && (LConst.mapConst k v d ⟨es⟩).wt && key.wt &&
        decide (key.sort = k) && decide (opTy.map (LMonoTy.arrowResult 2) = some v.toMonoTy) &&
        decide ((LConst.mapConst k v d ⟨es⟩).size ≤ maxLitSize) then
      some (selectChain md key d es)
    else none
  | _ => none

/-- `selectChain` builds expressions equal up to metadata at any two metadata. -/
private theorem selectChain_eraseMetadata (md₁ md₂ : CoreExprMetadata) (key d : LConst) :
    ∀ es, (selectChain md₁ key d es).eraseMetadata = (selectChain md₂ key d es).eraseMetadata
  | [] => by simp [selectChain, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | (k, v) :: rest => by
    have ih := selectChain_eraseMetadata md₁ md₂ key d rest
    simp only [selectChain]
    split
    · simp [LExpr.eraseMetadata, LExpr.replaceMetadata]
    · simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at ih ⊢
      rw [ih]

/-- `selectChain` has no free variables. -/
private theorem selectChain_getVars (md : CoreExprMetadata) (key d : LConst) :
    ∀ es, LExpr.LExpr.getVars (selectChain md key d es) = []
  | [] => rfl
  | (k, v) :: rest => by
    simp only [selectChain]
    split
    · rfl
    · simp [LExpr.LExpr.getVars, selectChain_getVars md key d rest]

/-- Arguments that are all constants are as many as their constants. -/
private theorem constArgs?_length : ∀ {args : List Expression.Expr} {cs : List LConst},
    LExpr.constArgs? args = some cs → args.length = cs.length
  | [], cs, h => by simp only [LExpr.constArgs?, Option.some.injEq] at h; subst h; rfl
  | a :: rest, cs, h => by
    cases a <;> simp only [LExpr.constArgs?, reduceCtorEq] at h
    obtain ⟨cs', h', rfl⟩ := Option.map_eq_some_iff.mp h
    simp [constArgs?_length h']

/-- What `selectChainEval` returns: the chain of a map literal and a key, which are its two
    arguments, under the conditions it checks. -/
theorem selectChainEval_some {md : CoreExprMetadata} {opTy : Option LMonoTy}
    {args : List Expression.Expr} {r : Expression.Expr} (h : selectChainEval md opTy args = some r) :
    ∃ k v d es key, LExpr.constArgs? args = some [.mapConst k v d ⟨es⟩, key] ∧
      key.hasData = true ∧ k.hasMap = false ∧ (LConst.mapConst k v d ⟨es⟩).wt = true ∧
      key.wt = true ∧ key.sort = k ∧ opTy.map (LMonoTy.arrowResult 2) = some v.toMonoTy ∧
      r = selectChain md key d es := by
  unfold selectChainEval at h
  split at h
  · rename_i k v d es key hc
    split at h
    · rename_i hchk
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hchk
      exact ⟨k, v, d, es, key, hc, hchk.1.1.1.1.1.1, hchk.1.1.1.1.1.2, hchk.1.1.1.1.2,
        hchk.1.1.1.2, hchk.1.1.2, hchk.1.2, h.symm⟩
    · cases h
  · cases h

end AggregateLitEval

mutual
/-- A collection literal as the expression that builds it from operators:
    `mapConst(d)` updated with the entries (the first entry outermost, since it is
    the one that counts), or `Sequence.empty()` built on with the elements in
    order. A datatype value is its operator, annotated with its signature, applied to its
    arguments. Any other constant is itself. -/
def litToOpExpr : LConst → Expression.Expr
  | .mapConst k v d ⟨xs⟩ =>
    let kt := k.toMonoTy
    let vt := v.toMonoTy
    litEntriesToOpExpr kt vt
      (.app default (.op default "mapConst" (some (.arrow vt (mapTy kt vt)))) (litToOpExpr d))
      xs
  | .sequenceConst a ⟨xs⟩ =>
    litElemsToOpExpr a.toMonoTy (.op default "Sequence.empty" (some (seqTy a.toMonoTy))) xs
  | .dataConst n as s ⟨xs⟩ =>
    litArgsToOpExpr
      (.op default ⟨n, default⟩ (some (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy))))) xs
  | c => .const default c
/-- `base` updated with the map entries `xs`, the first one outermost. -/
def litEntriesToOpExpr (kt vt : LMonoTy) (base : Expression.Expr) :
    List (LConst × LConst) → Expression.Expr
  | [] => base
  | (key, x) :: rest =>
    let updTy := LMonoTy.arrow (mapTy kt vt) (.arrow kt (.arrow vt (mapTy kt vt)))
    .app default
      (.app default (.app default (.op default "update" (some updTy))
        (litEntriesToOpExpr kt vt base rest)) (litToOpExpr key))
      (litToOpExpr x)
/-- `f` applied to the expressions of the constants `xs`, in order. -/
def litArgsToOpExpr (f : Expression.Expr) : List LConst → Expression.Expr
  | [] => f
  | x :: rest => litArgsToOpExpr (.app default f (litToOpExpr x)) rest
/-- `acc` with the sequence elements `xs` appended in order. -/
def litElemsToOpExpr (et : LMonoTy) (acc : Expression.Expr) : List LConst → Expression.Expr
  | [] => acc
  | x :: rest =>
    let buildTy := LMonoTy.arrow (seqTy et) (.arrow et (seqTy et))
    litElemsToOpExpr et
      (.app default (.app default (.op default "Sequence.build" (some buildTy)) acc)
        (litToOpExpr x))
      rest
end


/- A constant `Map` constructor with type `∀k, v. v → Map k v`.
   `mapConst(d)` returns a map where every key maps to the value `d`.
   Named `mapConst` (not `const`) to avoid colliding with the `const`
   declaration keyword in the Core grammar, which would otherwise make
   pretty-printed programs fail to re-parse. -/
def mapConstFunc : WFLFunc CoreLParams :=
  polyLitOp "mapConst" ["k", "v"]
    [("d", mty[%v])]
    (mapTy mty[%k] mty[%v])
    AggregateLitEval.mapConst
    (axioms := [
      eb[∀ (%v): -- %1 d
          (∀ (%k): -- %0 kk
            {(((~select : (Map %k %v) → %k → %v)
                ((~mapConst : %v → (Map %k %v)) %1)) %0)}
            (((~select : (Map %k %v) → %k → %v)
                ((~mapConst : %v → (Map %k %v)) %1)) %0) == %1)]
    ])

/-- The literal evaluator of `select`, at a canonical key sort (`polyLitOp` of
    `AggregateLitEval.mapSelect`). -/
def mapSelectLitFunc : WFLFunc CoreLParams :=
  polyLitOp "select" ["k", "v"]
    [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k])] mty[%v]
    AggregateLitEval.mapSelect

/-- The concrete evaluator of `select`: the literal of `mapSelectLitFunc`, else the chain of
    `AggregateLitEval.selectChainEval`. -/
@[expose] def mapSelectEval : ConcreteEval CoreLParams := fun md ty args =>
  ((mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md ty args).orElse fun _ =>
    AggregateLitEval.selectChainEval md ty args

/- A `Map` selection function with type `∀k, v. Map k v → k → v`. At a key sort without `Map` it
   evaluates to the literal value for a key holding no datatype value, and to the `ite` chain over
   the literal's entries (`AggregateLitEval.selectChain`) for a key holding one. -/
def mapSelectFunc : WFLFunc CoreLParams :=
  ⟨{ mapSelectLitFunc.func with concreteEval := some mapSelectEval }, {
    toFuncWF := mapSelectLitFunc.wf.toFuncWF
    constr_no_eval := by simp [mapSelectLitFunc, polyLitOp]
    typeArgs_no_gen_prefix := mapSelectLitFunc.wf.typeArgs_no_gen_prefix
    concreteEval_argmatch := by
      intro fn md opTy args res hfn hres
      cases hfn
      simp only [mapSelectEval] at hres
      cases hr : (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md opTy args with
      | some r =>
        exact mapSelectLitFunc.wf.concreteEval_argmatch _ md opTy args r rfl hr
      | none =>
        simp only [hr, Option.orElse] at hres
        obtain ⟨k, v, d, es, key, hc, -⟩ := AggregateLitEval.selectChainEval_some hres
        exact AggregateLitEval.constArgs?_length hc
    body_or_concreteEval := by simp [mapSelectLitFunc, polyLitOp]
    concreteEval_eraseMetadata := by
      intro fn hfn md1 md2 opTy args1 args2 res1 he hres
      cases hfn
      simp only [mapSelectEval] at hres ⊢
      cases hr1 : (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md1 opTy args1 with
      | some r =>
        simp only [hr1, Option.orElse] at hres; cases hres
        obtain ⟨r2, hr2, heq⟩ := mapSelectLitFunc.wf.concreteEval_eraseMetadata _ rfl md1 md2 opTy
          args1 args2 res1 he hr1
        exact ⟨r2, by simp [show (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md2
          opTy args2 = some r2 from hr2, Option.orElse], heq⟩
      | none =>
        simp only [hr1, Option.orElse] at hres
        cases hr2 : (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md2 opTy args2 with
        | some r =>
          obtain ⟨r', hr', -⟩ := mapSelectLitFunc.wf.concreteEval_eraseMetadata _ rfl md2 md1 opTy
            args2 args1 r he.symm hr2
          simp [show (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md1 opTy args1 =
            some r' from hr'] at hr1
        | none =>
          simp only [Option.orElse]
          unfold AggregateLitEval.selectChainEval at hres ⊢
          rw [← LExpr.constArgs?_eraseMetadata he]
          split at hres
          · split at hres
            · simp only [Option.some.injEq] at hres; subst hres
              rename_i hchk
              simp only [hchk, ↓reduceIte]
              exact ⟨_, rfl, AggregateLitEval.selectChain_eraseMetadata md1 md2 _ _ _⟩
            · cases hres
          · cases hres
    concreteEval_freeVars := by
      intro fn hfn md opTy args res hres z hz
      cases hfn
      simp only [mapSelectEval] at hres
      cases hr : (mapSelectLitFunc.func.concreteEval.getD fun _ _ _ => none) md opTy args with
      | some r =>
        simp only [hr, Option.orElse] at hres; cases hres
        exact mapSelectLitFunc.wf.concreteEval_freeVars _ rfl md opTy args res hr z hz
      | none =>
        simp only [hr, Option.orElse] at hres
        obtain ⟨k, v, d, es, key, -, -, -, -, -, -, -, rfl⟩ :=
          AggregateLitEval.selectChainEval_some hres
        simp [AggregateLitEval.selectChain_getVars] at hz
    shortCircuit_substFvars := by intro h; simp [Strata.DL.Util.FuncAttr.hasShortCircuit,
      mapSelectLitFunc, polyLitOp] at h }⟩

/- A `Map` update function with type `∀k, v. Map k v → k → v → Map k v`. -/
def mapUpdateFunc : WFLFunc CoreLParams :=
  polyLitOp "update" ["k", "v"]
    [("m", mapTy mty[%k] mty[%v]), ("i", mty[%k]), ("x", mty[%v])]
    (mapTy mty[%k] mty[%v])
    AggregateLitEval.mapUpdate
    (axioms := [
      -- updateSelect: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv
      eb[∀(Map %k %v):
          (∀ (%k):
            (∀ (%v):{
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1)}
              (((~select : (Map %k %v) → %k → %v)
                ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %2) %1) %0)) %1) == %0))],
      -- updatePreserve: forall m: Map k v, okk: k, kk: k, vv: v :: okk != kk ==> m[kk := vv][okk]
      --   == m[okk]
      eb[∀ (Map %k %v): -- %3 m
          (∀ (%k): -- %2 okk
            (∀ (%k): -- %1 kk
              (∀ (%v): -- %0 vv
                  -- okk != kk ==> ...
                  (if (%2 == %1) then
                      #true
                  else
                    -- if keys are different, the value of the other key one remains unchanged
                    -- (select (update m kk vv) okk) ==  (select m okk)
                    ((((~select : (Map %k %v) → %k → %v)
                        ((((~update : (Map %k %v) → %k → %v → (Map %k %v)) %3) %1) %0)
                      ) %2)
                    ==
                    ((((~select : (Map %k %v) → %k → %v) %3) %2)))
                    ))))]
    ])

/-! ## `Set` operations

Every operation is characterized *pointwise through membership*: each axiom states what
`Set.contains` yields on the result. That is the whole specification: the axioms give
two sets with the same members the same membership in the result of every `Set.*`
operation. Equality and other functions over sets can still tell such sets apart unless
the encoding is extensional (see `setTy`).

`Set.contains` itself carries no axiom: it is the primitive the others are defined against.

Each axiom is triggered on the `Set.contains`-of-the-operation pattern, so it fires exactly
when a membership question is asked about a constructed set, rather than eagerly on every
construction.

Note what is deliberately absent: there is no cardinality operation. `Set.card` cannot be
axiomatized pointwise (it needs induction over a finite domain), so adding it would mean
either an unsound partial axiomatization or real finite-set support in the encoder. It is
left out until the encoder targets a set theory that provides it. -/

/- The empty `Set`, with type `∀a. Set a`.
   Like `Sequence.empty` this takes no value arguments, so the element type is not
   inferable from a call site and must come from the `.op` type annotation. -/
def setEmptyFunc : WFLFunc CoreLParams :=
  polyUneval "Set.empty" ["a"] [] (setTy mty[%a])
    (axioms := [
      -- forall x :: !contains(empty, x)
      eb[∀ (%a): -- %0 x
          {(((~Set.contains : (Set %a) → %a → bool)
              (~Set.empty : (Set %a))) %0)}
          (((~Set.contains : (Set %a) → %a → bool)
              (~Set.empty : (Set %a))) %0) == #false]
    ])

def setContainsFunc : WFLFunc CoreLParams :=
  polyUneval "Set.contains" ["a"]
    [("s", setTy mty[%a]), ("x", mty[%a])] mty[bool]

/- A `Set` insertion with type `∀a. Set a → a → Set a`. Returns a NEW set; `s` is
   unchanged, which is what makes the type immutable. -/
def setInsertFunc : WFLFunc CoreLParams :=
  polyUneval "Set.insert" ["a"]
    [("s", setTy mty[%a]), ("x", mty[%a])] (setTy mty[%a])
    (axioms := [
      -- forall s, x, y :: contains(insert(s, x), y) == (y == x || contains(s, y))
      eb[∀ (Set %a): -- %2 s
          (∀ (%a):    -- %1 x
            (∀ (%a):  -- %0 y
              {(((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.insert : (Set %a) → %a → (Set %a)) %2) %1)) %0)}
              (((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.insert : (Set %a) → %a → (Set %a)) %2) %1)) %0)
              ==
              (((~Bool.Or : bool → bool → bool)
                (%0 == %1))
                (((~Set.contains : (Set %a) → %a → bool) %2) %0))))]
    ])

/- A `Set` removal with type `∀a. Set a → a → Set a`. Removing an absent element is a
   no-op rather than an error, so the operation is total. -/
def setRemoveFunc : WFLFunc CoreLParams :=
  polyUneval "Set.remove" ["a"]
    [("s", setTy mty[%a]), ("x", mty[%a])] (setTy mty[%a])
    (axioms := [
      -- forall s, x, y :: contains(remove(s, x), y) == (!(y == x) && contains(s, y))
      eb[∀ (Set %a): -- %2 s
          (∀ (%a):    -- %1 x
            (∀ (%a):  -- %0 y
              {(((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.remove : (Set %a) → %a → (Set %a)) %2) %1)) %0)}
              (((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.remove : (Set %a) → %a → (Set %a)) %2) %1)) %0)
              ==
              (((~Bool.And : bool → bool → bool)
                ((~Bool.Not : bool → bool) (%0 == %1)))
                (((~Set.contains : (Set %a) → %a → bool) %2) %0))))]
    ])

def setUnionFunc : WFLFunc CoreLParams :=
  polyUneval "Set.union" ["a"]
    [("s", setTy mty[%a]), ("t", setTy mty[%a])] (setTy mty[%a])
    (axioms := [
      -- forall s, t, y :: contains(union(s, t), y) == (contains(s, y) || contains(t, y))
      eb[∀ (Set %a): -- %2 s
          (∀ (Set %a): -- %1 t
            (∀ (%a):   -- %0 y
              {(((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.union : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)}
              (((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.union : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)
              ==
              (((~Bool.Or : bool → bool → bool)
                (((~Set.contains : (Set %a) → %a → bool) %2) %0))
                (((~Set.contains : (Set %a) → %a → bool) %1) %0))))]
    ])

def setIntersectFunc : WFLFunc CoreLParams :=
  polyUneval "Set.intersect" ["a"]
    [("s", setTy mty[%a]), ("t", setTy mty[%a])] (setTy mty[%a])
    (axioms := [
      -- forall s, t, y :: contains(intersect(s, t), y) == (contains(s, y) && contains(t, y))
      eb[∀ (Set %a): -- %2 s
          (∀ (Set %a): -- %1 t
            (∀ (%a):   -- %0 y
              {(((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.intersect : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)}
              (((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.intersect : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)
              ==
              (((~Bool.And : bool → bool → bool)
                (((~Set.contains : (Set %a) → %a → bool) %2) %0))
                (((~Set.contains : (Set %a) → %a → bool) %1) %0))))]
    ])

def setDifferenceFunc : WFLFunc CoreLParams :=
  polyUneval "Set.difference" ["a"]
    [("s", setTy mty[%a]), ("t", setTy mty[%a])] (setTy mty[%a])
    (axioms := [
      -- forall s, t, y :: contains(difference(s, t), y) == (contains(s, y) && !contains(t, y))
      eb[∀ (Set %a): -- %2 s
          (∀ (Set %a): -- %1 t
            (∀ (%a):   -- %0 y
              {(((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.difference : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)}
              (((~Set.contains : (Set %a) → %a → bool)
                  (((~Set.difference : (Set %a) → (Set %a) → (Set %a)) %2) %1)) %0)
              ==
              (((~Bool.And : bool → bool → bool)
                (((~Set.contains : (Set %a) → %a → bool) %2) %0))
                ((~Bool.Not : bool → bool)
                  (((~Set.contains : (Set %a) → %a → bool) %1) %0)))))]
    ])

/- A `Sequence` length function with type `∀a. Sequence a → int`. -/
def seqLengthFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.length" ["a"]
    [("s", seqTy mty[%a])] mty[int]
    AggregateLitEval.seqLength
    (axioms := [
      -- length(s) >= 0
      eb[∀ (Sequence %a): -- %0 s
        {((~Sequence.length : (Sequence %a) → int) %0)}
        (((~Int.Ge : int → int → bool)
          ((~Sequence.length : (Sequence %a) → int) %0))
          #0)]
    ])

/- An empty `Sequence` constructor with type `∀a. Sequence a`.
   `Sequence.empty<A>()` returns an empty sequence of element type `A`.
   The `<A>` is surface syntax produced by Grammar.lean and consumed by
   Translate.lean; this function itself takes no value parameters. -/
def seqEmptyFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.empty" ["a"] [] (seqTy mty[%a])
    AggregateLitEval.seqEmpty
    (axioms := [
      -- length(empty()) == 0
      eb[((~Sequence.length : (Sequence %a) → int)
            (~Sequence.empty : (Sequence %a))) == #0]
    ])

/- Rename one operator throughout a list of axioms. Purely syntactic. -/
private def renameOpIn («from» to : String) (axs : List Expression.Expr) :
    List Expression.Expr :=
  axs.map (·.substOps (Strata.Util.HMap.ofList
    [(⟨«from», ()⟩, fun ty => .op (ExprSourceLoc.synthesized "factory") to ty)]))

/- Each select-of-constructor axiom, paired with its `Sequence.select!` mirror
   (same axiom with `Sequence.select` renamed), so the unsafe selector reasons
   through constructors identically to the checked one. -/
private def withSelectBang (axs : List Expression.Expr) : List Expression.Expr :=
  axs ++ renameOpIn "Sequence.select" "Sequence.select!" axs

/- A `Sequence` append function with type `∀a. Sequence a → Sequence a → Sequence a`. -/
def seqAppendFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.append" ["a"]
    [("s1", seqTy mty[%a]), ("s2", seqTy mty[%a])]
    (seqTy mty[%a])
    AggregateLitEval.seqAppend
    (axioms :=
      -- length(append(s0, s1)) == length(s0) + length(s1)
      [ eb[∀ (Sequence %a): -- %1 s0
          (∀ (Sequence %a): -- %0 s1
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %1) %0))}
            ((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %1) %0))
            ==
            (((~Int.Add : int → int → int)
              ((~Sequence.length : (Sequence %a) → int) %1))
              ((~Sequence.length : (Sequence %a) → int) %0)))] ]
      ++ withSelectBang [
      -- 0 <= n < length(s0) ==> select(append(s0,s1), n) == select(s0, n)
      eb[∀ (Sequence %a): -- %2 s0
          (∀ (Sequence %a): -- %1 s1
            (∀ (int): -- %0 n
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1))
                      %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int)
                      %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1))
                      %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))],
      -- select(append(s0, s1), n):
      --   n >= length(s0) && n < length(s0) + length(s1)
      --     ==> select(append(s0,s1), n) == select(s1, n - length(s0))
      eb[∀ (Sequence %a): -- %2 s0
          (∀ (Sequence %a): -- %1 s1
            (∀ (int): -- %0 n
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1))
                      %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int)
                      %2)))
                    (((~Int.Lt : int → int → bool) %0)
                      (((~Int.Add : int → int → int)
                        ((~Sequence.length : (Sequence %a) → int) %2))
                        ((~Sequence.length : (Sequence %a) → int) %1))))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.append : (Sequence %a) → (Sequence %a) → (Sequence %a)) %2) %1))
                      %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %1)
                    (((~Int.Sub : int → int → int) %0) ((~Sequence.length : (Sequence %a) → int)
                      %2)))
              else #true))]
      ])

/-! ### Sequence bounds preconditions

`Sequence.select` / `update` / `take` / `drop` carry bounds
preconditions; the other `Sequence.*` ops are total. -/

/-- Choice of upper-bound operator in `mkSeqBoundsPrecond`: `Lt` (strict) for
    `Sequence.select`/`update`, `Le` (non-strict) for `Sequence.take`/`drop`.
    Restricting the parameter to this inductive rather than taking an
    arbitrary `WFLFunc` or `LExpr` makes it impossible to attach a partial
    operator (which would create a nested precondition obligation) by
    accident. -/
private inductive SeqBoundKind where | Lt | Le

/-- Returns the *upper-bound* comparison for `mkSeqBoundsPrecond`.
    The lower bound is always `0 ≤ x` (see `mkSeqBoundsPrecond`), so this
    method characterises only the upper comparison. A future partial
    Sequence op requiring a non-`int` comparison (e.g. a bitvector variant)
    should introduce a separate helper rather than extend this enum. -/
private def SeqBoundKind.upperOpExpr : SeqBoundKind → LExpr CoreLParams.mono
  | .Lt => (intLtFunc (T := CoreLParams)).opExpr
  | .Le => (intLeFunc (T := CoreLParams)).opExpr

/-- Precondition `0 <= varName && varName `k.upperOpExpr` Sequence.length(seqName)`.

    `seqName` defaults to `"s"` since all four current call sites
    (`Sequence.select`/`update`/`take`/`drop`) name their `Sequence a` input
    that way. The parameter exists so a future partial Sequence op with a
    different input name need only pass it explicitly rather than rely on a
    hidden string literal. Either way, mismatches between the function's
    declared inputs and the names used here are caught at elaboration by
    `polyUneval`'s `h_precond` free-vars check. -/
private def mkSeqBoundsPrecond
    (varName : String) (k : SeqBoundKind) (seqName : String := "s") :
    Strata.DL.Util.FuncPrecondition (LExpr CoreLParams.mono) CoreLParams.Metadata :=
  let sVar  : LExpr CoreLParams.mono := .fvar default seqName (some (seqTy mty[%a]))
  let xVar  : LExpr CoreLParams.mono := .fvar default varName (some mty[int])
  let zero  : LExpr CoreLParams.mono := .intConst default 0
  let lenS  : LExpr CoreLParams.mono := .app default seqLengthFunc.opExpr sVar
  let lower : LExpr CoreLParams.mono :=
    .app default (.app default (intLeFunc (T := CoreLParams)).opExpr zero) xVar
  let upper : LExpr CoreLParams.mono :=
    .app default (.app default k.upperOpExpr xVar) lenS
  ⟨.app default (.app default (boolAndFunc (T := CoreLParams)).opExpr lower) upper,
   default⟩

/- A `Sequence` selection function with type `∀a. Sequence a → int → a`.
   Partial: requires `0 <= i && i < Sequence.length(s)`.

   Its one axiom states that `Sequence.select!` equals it at every argument, out
   of range included: Core identifies each checked sequence operation with its
   total twin, which is what lets `SeqTotalize` rewrite one into the other
   anywhere, in a function body, an axiom or a lemma as well as in a statement.
   An out-of-range fact about either form is therefore a fact about the other:
   axioms that give `select(s, i)` and `select!(s, i)` different values at the same
   out-of-range `i` contradict each other, and `PrecondElim` checks no bounds in an
   axiom. The axiom belongs to `Sequence.select`, so the
   encoder sends it only for a query that uses `Sequence.select`: a program
   written with `Sequence.select!` alone pays nothing for it. It mentions
   `Sequence.select!`, which carries no axioms of its own, so it pulls in nothing
   else. It is triggered on the unchecked call, so a query using only
   `Sequence.select` never instantiates it. -/
def seqSelectFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.select" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int])] mty[%a]
    AggregateLitEval.seqSelect
    (axioms := [
      -- select!(s, i) == select(s, i)
      eb[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 i
            {(((~Sequence.select! : (Sequence %a) → int → %a) %1) %0)}
            (((~Sequence.select! : (Sequence %a) → int → %a) %1) %0)
            ==
            (((~Sequence.select : (Sequence %a) → int → %a) %1) %0))]
    ])
    (preconditions := [mkSeqBoundsPrecond "i" .Lt])

/- The total twins (`select!`, `update!`, `take!`, `drop!`) share the axioms of
   their checked forms, renamed: `withSelectBang` states every select axiom in
   both forms, and each twin below takes the checked list with its own name
   substituted, all but the last axiom, which is the agreement of the checked form
   with the twin. Keep them equivalent. After `PrecondElim` the `SeqTotalize`
   phase rewrites every checked operation of the program to its twin. The axioms
   stated with `withSelectBang` still mention the checked `Sequence.select`, so a
   query that uses `append`, `build`, `update`, `contains`, `take` or `drop` also
   declares it and receives its agreement axiom. -/

/- An *unsafe* total variant of `Sequence.select`: no bounds precondition, so
   no out-of-bounds obligation per call site; out of range, its value is that of
   `Sequence.select`, which no other axiom constrains there. Shares
   `Sequence.select`'s interaction axioms (mirrored on the constructor functions),
   so it reasons through constructors identically. -/
def seqSelectUnsafeFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.select!" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int])] mty[%a]
    AggregateLitEval.seqSelect

/- A `Sequence` build (snoc) function with type `∀a. Sequence a → a → Sequence a`.
   `build(s, v)` appends a single element `v` to the end of `s`. -/
def seqBuildFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.build" ["a"]
    [("s", seqTy mty[%a]), ("v", mty[%a])]
    (seqTy mty[%a])
    AggregateLitEval.seqBuild
    (axioms :=
      -- length(build(s, v)) == 1 + length(s)
      [ eb[∀ (Sequence %a): -- %1 s
          (∀ (%a): -- %0 v
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %1) %0))}
            ((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %1) %0))
            ==
            (((~Int.Add : int → int → int)
              #1)
              ((~Sequence.length : (Sequence %a) → int) %1)))] ]
      ++ withSelectBang [
      -- i == length(s) ==> select(build(s,v), i) == v
      eb[∀ (Sequence %a): -- %2 s
          (∀ (%a): -- %1 v
            (∀ (int): -- %0 i
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)}
              if (%0 == ((~Sequence.length : (Sequence %a) → int) %2))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)
                == %1
              else #true))],
      -- 0 <= i < length(s) ==> select(build(s,v), i) == select(s, i)
      eb[∀ (Sequence %a): -- %2 s
          (∀ (%a): -- %1 v
            (∀ (int): -- %0 i
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0)
                      ((~Sequence.length : (Sequence %a) → int) %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.build : (Sequence %a) → %a → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))]
      ])

/- A `Sequence` update function with type `∀a. Sequence a → int → a → Sequence a`.
   `update(s, i, v)` returns a sequence identical to `s` except at index `i` where the value is `v`.
   Partial: requires `0 <= i && i < Sequence.length(s)`. -/
def seqUpdateFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.update" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int]), ("v", mty[%a])]
    (seqTy mty[%a])
    AggregateLitEval.seqUpdate
    (axioms :=
      -- length(update(s, i, v)) == length(s)
      [ eb[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 i
            (∀ (%a): -- %0 v
              {((~Sequence.length : (Sequence %a) → int)
                ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0))}
              ((~Sequence.length : (Sequence %a) → int)
                ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0))
              ==
              ((~Sequence.length : (Sequence %a) → int) %2)))] ]
      ++ withSelectBang [
      -- 0 <= i < length(s) ==> select(update(s, i, v), i) == v  (same index)
      eb[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 i
            (∀ (%a): -- %0 v
              {(((~Sequence.select : (Sequence %a) → int → %a)
                  ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)) %1)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %1) #0))
                    (((~Int.Lt : int → int → bool) %1)
                      ((~Sequence.length : (Sequence %a) → int) %2)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0))
                      %1)
                == %0
              else #true))],
      -- 0 <= n < length(s) && n != i ==> select(update(s, i, v), n) == select(s, n)
      eb[∀ (Sequence %a): -- %3 s
          (∀ (int): -- %2 i
            (∀ (%a): -- %1 v
              (∀ (int): -- %0 n
                {(((~Sequence.select : (Sequence %a) → int → %a)
                    ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %3) %2) %1))
                      %0)}
                if (((~Bool.And : bool → bool → bool)
                      (((~Bool.And : bool → bool → bool)
                        (((~Int.Ge : int → int → bool) %0) #0))
                        (((~Int.Lt : int → int → bool) %0)
                          ((~Sequence.length : (Sequence %a) → int) %3))))
                      ((~Bool.Not : bool → bool) (%0 == %2)))
                then
                  (((~Sequence.select : (Sequence %a) → int → %a)
                      ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %3) %2)
                        %1)) %0)
                  ==
                  (((~Sequence.select : (Sequence %a) → int → %a) %3) %0)
                else #true)))]
      ]
      -- The agreement with the total twin, last (see `seqSelectFunc`):
      -- update!(s, i, v) == update(s, i, v)
      ++ [ eb[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 i
            (∀ (%a): -- %0 v
              {((((~Sequence.update! : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)}
              ((((~Sequence.update! : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)
              ==
              ((((~Sequence.update : (Sequence %a) → int → %a → (Sequence %a)) %2) %1) %0)))] ])
    (preconditions := [mkSeqBoundsPrecond "i" .Lt])

/- An *unsafe* total variant of `Sequence.update`: no bounds precondition, so no
   out-of-bounds obligation per call site. The length axiom holds for any index, and
   the select-of-update axioms stay guarded by their own bounds. -/
def seqUpdateUnsafeFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.update!" ["a"]
    [("s", seqTy mty[%a]), ("i", mty[int]), ("v", mty[%a])]
    (seqTy mty[%a])
    AggregateLitEval.seqUpdate
    (axioms :=
      renameOpIn "Sequence.update" "Sequence.update!" seqUpdateFunc.func.axioms.dropLast)

/- A `Sequence` contains function with type `∀a. Sequence a → a → bool`.
   `contains(s, v)` is true iff there exists an index `i` such that `select(s, i) == v`. -/
def seqContainsFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.contains" ["a"]
    [("s", seqTy mty[%a]), ("v", mty[%a])] mty[bool]
    AggregateLitEval.seqContains
    (axioms := withSelectBang [
      -- contains(s, v) <==> exists i :: 0 <= i < length(s) && select(s, i) == v
      eb[∀ (Sequence %a): -- %1 s
          (∀ (%a): -- %0 v
            {(((~Sequence.contains : (Sequence %a) → %a → bool) %1) %0)}
            (((~Sequence.contains : (Sequence %a) → %a → bool) %1) %0)
            ==
            (∃ (int): -- %0 i (inside this quantifier: s=%2, v=%1, i=%0)
              (((~Bool.And : bool → bool → bool)
                (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Lt : int → int → bool) %0) ((~Sequence.length : (Sequence %a) → int)
                    %2))))
                ((((~Sequence.select : (Sequence %a) → int → %a) %2) %0) == %1))))]
    ])

/- A `Sequence` take function with type `∀a. Sequence a → int → Sequence a`.
   `take(s, n)` returns the first `n` elements of `s`.
   Partial: requires `0 <= n && n <= Sequence.length(s)`. -/
def seqTakeFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.take" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    AggregateLitEval.seqTake
    (axioms :=
      -- 0 <= n <= length(s) ==> length(take(s, n)) == n
      [ eb[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %1) %0))}
            if (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Le : int → int → bool) %0)
                    ((~Sequence.length : (Sequence %a) → int) %1)))
            then
              ((~Sequence.length : (Sequence %a) → int)
                (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %1) %0))
              == %0
            else #true)] ]
      ++ withSelectBang [
      -- select(take(s, n), j) == select(s, j)  (when 0 <= j < n)
      eb[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 n
            (∀ (int): -- %0 j
              {(((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0) %1))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2) %0)
              else #true))]
      ]
      -- The agreement with the total twin, last (see `seqSelectFunc`):
      -- take!(s, n) == take(s, n)
      ++ [ eb[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {(((~Sequence.take! : (Sequence %a) → int → (Sequence %a)) %1) %0)}
            (((~Sequence.take! : (Sequence %a) → int → (Sequence %a)) %1) %0)
            ==
            (((~Sequence.take : (Sequence %a) → int → (Sequence %a)) %1) %0))] ])
    (preconditions := [mkSeqBoundsPrecond "n" .Le])

/- An *unsafe* total variant of `Sequence.take`. Its length axiom keeps
   `Sequence.take`'s `0 <= n <= length(s)` guard: `Sequence.length` is axiomatised
   as non-negative, so an unguarded `length(take!(s, n)) == n` would be false for a
   negative `n` and make every goal provable. Out of range, `take!` is `take`, which no
   other axiom constrains there. -/
def seqTakeUnsafeFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.take!" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    AggregateLitEval.seqTake
    (axioms :=
      renameOpIn "Sequence.take" "Sequence.take!" seqTakeFunc.func.axioms.dropLast)

/- A `Sequence` drop function with type `∀a. Sequence a → int → Sequence a`.
   `drop(s, n)` returns the sequence with the first `n` elements removed.
   Partial: requires `0 <= n && n <= Sequence.length(s)`. -/
def seqDropFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.drop" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    AggregateLitEval.seqDrop
    (axioms :=
      -- 0 <= n <= length(s) ==> length(drop(s, n)) == length(s) - n
      [ eb[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {((~Sequence.length : (Sequence %a) → int)
              (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %1) %0))}
            if (((~Bool.And : bool → bool → bool)
                  (((~Int.Ge : int → int → bool) %0) #0))
                  (((~Int.Le : int → int → bool) %0)
                    ((~Sequence.length : (Sequence %a) → int) %1)))
            then
              ((~Sequence.length : (Sequence %a) → int)
                (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %1) %0))
              ==
              (((~Int.Sub : int → int → int)
                ((~Sequence.length : (Sequence %a) → int) %1))
                %0)
            else #true)] ]
      ++ withSelectBang [
      -- 0 <= j < length(s) - n ==> select(drop(s, n), j) == select(s, j + n)
      eb[∀ (Sequence %a): -- %2 s
          (∀ (int): -- %1 n
            (∀ (int): -- %0 j
              {(((~Sequence.select : (Sequence %a) → int → %a)
                  (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)}
              if (((~Bool.And : bool → bool → bool)
                    (((~Int.Ge : int → int → bool) %0) #0))
                    (((~Int.Lt : int → int → bool) %0)
                      (((~Int.Sub : int → int → int)
                        ((~Sequence.length : (Sequence %a) → int) %2))
                        %1)))
              then
                (((~Sequence.select : (Sequence %a) → int → %a)
                    (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %2) %1)) %0)
                ==
                (((~Sequence.select : (Sequence %a) → int → %a) %2)
                    (((~Int.Add : int → int → int) %0) %1))
              else #true))]
      ]
      -- The agreement with the total twin, last (see `seqSelectFunc`):
      -- drop!(s, n) == drop(s, n)
      ++ [ eb[∀ (Sequence %a): -- %1 s
          (∀ (int): -- %0 n
            {(((~Sequence.drop! : (Sequence %a) → int → (Sequence %a)) %1) %0)}
            (((~Sequence.drop! : (Sequence %a) → int → (Sequence %a)) %1) %0)
            ==
            (((~Sequence.drop : (Sequence %a) → int → (Sequence %a)) %1) %0))] ])
    (preconditions := [mkSeqBoundsPrecond "n" .Le])

/- An *unsafe* total variant of `Sequence.drop`, keeping `Sequence.drop`'s bounds
   guard on the length axiom for the reason given on `seqTakeUnsafeFunc`. -/
def seqDropUnsafeFunc : WFLFunc CoreLParams :=
  polyLitOp "Sequence.drop!" ["a"]
    [("s", seqTy mty[%a]), ("n", mty[int])]
    (seqTy mty[%a])
    AggregateLitEval.seqDrop
    (axioms :=
      renameOpIn "Sequence.drop" "Sequence.drop!" seqDropFunc.func.axioms.dropLast)

end -- public section

end Core
