/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init
public import Strata.DL.SMT.Lean.Query
import all Strata.DL.SMT.Lean.Query
import all Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTypedSMTQuery
import all Strata.DL.SMT.Term
import all Strata.Util.OrderedSet
import all Strata.Util.OrderedSetProps

/-!
# Preparation reflects entailment, on well-formed queries

`prepareTerms` turns the assembled query, which is meant to be the query the solver was sent
(that is tested, not proved), into the prepared query. The exported file states a translation
of the prepared query to Lean, which is not proved either (see below).
`prepareTerms_sound` is the direction a proof of that file relies on: when the prepared query
entails its goal, so does the assembled query (`completeContext` of the obligation's context,
definitions and declarations) with the original assumptions and goal. The converse is not
proved. The statement uses Strata's typed SMT semantics (`Strata.SMT.DenoteTyped`) on both
sides: a query is read as an `SMTQuery`, and entailment (`SMTQuery.EntailsObl`) quantifies over
every sort interpretation, array theory, interpretation of the uninterpreted functions that
respects the definitions, variable environment, and completion of integer division and modulo
by zero.

Its hypotheses `hwf` and `hwf'` are that the assembled query and the prepared query are well
formed (`SMTQuery.WF`); nothing checks them at run time, and `hwf` covers the whole assembled
query, including the definitions and declarations pruning drops.

**What the theorem covers.** After assembling, `prepareTerms` prunes the query
(`retainFunctions`: it drops the declarations and definitions that the goal, the assumptions and
the context's axioms do not reach), filters it (`admissible`, which only refuses a query and
changes nothing), and normalizes it (`normalizeTerm`, applied to the goal, the assumptions, and
the axioms and definition bodies of the pruned context). It also empties the context's sort
declarations and keeps only the sort aliases the pruned query reaches; `toSMTQuery` ignores the
aliases, and neither `SMTQuery.WF` nor `SMTQuery.EntailsObl` reads the sort declarations. Of the
normalization rules the theorem covers only the one for `distinct` of two or more operands, which
becomes the conjunction of the pairwise disequalities; the other rules have inputs outside
`SMTQuery.WF` and are pinned by `QueryTests`, not proved (below). A binary integer `div` or `mod`
is left as it is.

**The fragment.** The theorem's hypotheses are `SMTQuery.WF` (module
`Strata.DL.SMT.DenoteTypedSMTQuery`) of `toSMTQuery ctx assumptions goal`. `toSMTQuery` makes
every declared symbol of the context (the obligation's declarations among them) a declared
function, every definition of the context (the obligation's definitions among them) a function
definition, in the context's order, and the context's axioms function axioms; it ignores sort
aliases. On such a query `SMTQuery.WF` requires:

- the declared and defined names are distinct, and none is `$__bv<n>` for a natural number `<n>`
  written in decimal without leading zeros (`$__bv03` is allowed);
- each definition body type-checks to the definition's declared sort, against the declared
  symbols, the definitions before it in the context's order, and its own parameters;
- every axiom, every assumption and the goal type-check to `Bool` (not merely type-check).

All three use `Term.typeCheck` (module `Strata.DL.SMT.DenoteTyped`) with no declared sorts. That
judgment admits exactly:

- sorts, of every term, quantified variable and applied function's signature: `Bool`, `Int`,
  `String`, `BitVec n`; `Option τ` and `Array κ ν` (the built-in name, two arguments) of admitted
  sorts. Not `Real`, `RegLan`, uninterpreted sorts, sort aliases or datatypes. A function that
  is declared and never applied, and a definition parameter that is never used, are not checked.
- terms:
  - literals of `Bool`, `Int`, `String` and `BitVec n`;
  - a variable whose innermost binder of that name, an enclosing quantifier or a parameter of the
    definition, has the variable's sort. An outer binder of the right sort does not count when an
    inner one of that name has another, and within one binder list the last binder of a name is
    the innermost;
  - an application of a declared or defined function, with the declared argument and result
    sorts, whose name no enclosing quantified variable or definition parameter has;
  - `not` of one `Bool`; `and`, `or`, `=>` of exactly two `Bool`s; `=` of exactly two terms of
    one sort; `ite` of a `Bool` and two terms of one sort;
  - integer negation of one `Int`; `+`, `-`, `*`, `div`, `mod` of exactly two `Int`s; `<=`, `<`,
    `>=`, `>` of exactly two `Int`s;
  - `distinct` of two or more terms of one sort;
  - `forall` and `exists` with a `Bool` body, admitted binder sorts and well-typed triggers;
  - `none` and `some`; `select` and `store` on an `Array`;
  - in each of these operator applications, the result sort written on the term must be the sort
    the operator gives: `Bool` for `not`, `and`, `or`, `=>`, `=`, the comparisons and `distinct`;
    `Int` for negation and the arithmetic; the sort of the branches for `ite`; the value sort for
    `select`; the array's own sort for `store`.

Everything else is outside: `abs`, real arithmetic, every bit-vector, string and regex
operation, `option_get`, datatype operations, and every other number of operands.

On a query outside the fragment the theorem says nothing. So the normalization rules for `and`/`or`
with fewer than two operands, for n-ary chains, for n-ary `div` and for `distinct` of zero or one
operand are not covered: their input is never well formed, so the proof still compiles when the
term any of them returns is changed (a change to which terms a rule applies to can reach the
fragment, and the proof covers that); `QueryTests` pins their output instead. The semantics reads
SMT strings as Lean strings, which the solver's are not; preparation refuses strings, so no
exported query relies on that reading.

**The translation to Lean.** The theorem says nothing about the translation to Lean
(`translateQuery`) or about printing. When the query uses integer `div` or `mod`, the translator
gives a division or modulo by zero the value of one of two functions that the proposition
quantifies over, `divByZero` and `modByZero`: it writes `x div y` as
`if y = 0 then divByZero x else x / y`, and `x mod y` likewise with `modByZero` and `%`. That
matches Strata's semantics, where a division or modulo by zero is left to the interpretation:
`EntailsObl` quantifies over the completions (`divByZero` and `modByZero` there, `dz` and `mz` in
the proofs below), and `x div y` denotes `if y = 0 then dz x else x / y`. That the translation
has this meaning is tested, not proved.

The proof has three parts. The stage lemmas (`retainFunctions_eq`, `prepareTerms_eq`) read off
what `prepareTerms` built: the prepared assumptions and goal are the normalized originals, and
every prepared axiom and definition is the normalization of an axiom or definition of the
assembled query. `denote_normalizeTerm` shows that normalization preserves the denotation of a
well-typed term under the same interpretation. `entails_of_normalize` lifts that to queries: an
interpretation that respects the assembled query's definitions and satisfies its axioms and
assumptions also respects the prepared query's definitions and satisfies its axioms and
assumptions, since each of them is the normalization of one of the assembled query's (the
declarations and definitions pruning drops impose nothing on the prepared query). So it satisfies
the prepared goal, which denotes what the original goal does.
-/

namespace Strata.SMT.LeanExport

open Strata.SMT.DenoteTyped
open Classical

/-- The query `(ctx, assumptions, goal)` as the emitter groups it: the context's declarations,
definitions and axioms, then the assumptions and the goal. The obligation's own declarations
and definitions have already been folded into `ctx` by `completeContext`. -/
def toSMTQuery (ctx : Core.SMT.Context) (assumptions : List Term) (goal : Term) : SMTQuery where
  sorts := ctx.sorts.toList
  datatypes := []
  fnDecls := ctx.ufs.toList
  fnDefs := ctx.ifs.toList
  fnAxioms := ctx.axms.toList
  varDecls := []
  varDefs := []
  assumptions := assumptions
  obl := goal

/-! ## What each stage of `prepareTerms` builds -/

open Strata.Util.OrderedKeyedSet in
/-- The axioms of `mapContextTerms f ctx`, which applies `f` to every axiom and definition
body of `ctx`, are exactly the results of `f` on the axioms of `ctx`. -/
private theorem mem_mapContextTerms_axms {f : Term → Term} {ctx : Core.SMT.Context} {a : Term} :
    a ∈ (mapContextTerms f ctx).axms.toList ↔ ∃ a₀ ∈ ctx.axms.toList, a = f a₀ := by
  simp only [mapContextTerms, Util.OrderedSet.toList, Util.OrderedSet.ofArrayUnchecked,
    toList_ofArrayUnchecked, Array.toList_map, List.mem_map]
  exact ⟨fun ⟨a₀, h, e⟩ => ⟨a₀, h, e.symm⟩, fun ⟨a₀, h, e⟩ => ⟨a₀, h, e.symm⟩⟩

open Strata.Util.OrderedKeyedSet in
/-- The definitions of `mapContextTerms f ctx`, which applies `f` to every axiom and definition
body of `ctx`, are exactly those of `ctx` with `f` applied to the body; the name, the parameters
and the result sort stay the same. -/
private theorem mem_mapContextTerms_ifs {f : Term → Term} {ctx : Core.SMT.Context} {d : IF} :
    d ∈ (mapContextTerms f ctx).ifs.toList ↔
      ∃ d₀ ∈ ctx.ifs.toList, d = { d₀ with body := f d₀.body } := by
  simp only [mapContextTerms, toList_ofArrayUnchecked, Array.toList_map, List.mem_map,
    ← toList_eq_toArray_toList]
  exact ⟨fun ⟨d₀, h, e⟩ => ⟨d₀, h, e.symm⟩, fun ⟨d₀, h, e⟩ => ⟨d₀, h, e.symm⟩⟩

open Strata.Util.OrderedKeyedSet in
/-- Pruning a context to the functions in `needed` (`retainedContext`) adds no definition: every
definition of the pruned context is one of the original context, unchanged. -/
private theorem mem_retainedContext_ifs {ctx : Core.SMT.Context} {needed : Std.HashSet UF} {d : IF}
    (h : d ∈ (retainedContext ctx needed).ifs.toList) : d ∈ ctx.ifs.toList := by
  simp only [retainedContext, toList_ofArrayUnchecked, Array.toList_filter, List.mem_filter,
    ← toList_eq_toArray_toList] at h
  exact h.1

/-- A successful pruning `retainFunctions ctx roots` returns `ctx` restricted to the declarations
and definitions that `roots` and the axioms of `ctx` reach, directly or through definition bodies
(`retainedContext` of `neededFunctions`). Its checks, that every needed function is declared or
defined and that no kept definition is recursive, only refuse a context; they do not change it. -/
private theorem retainFunctions_eq {ctx ctx' : Core.SMT.Context} {roots : List Term}
    (h : retainFunctions ctx roots = .ok ctx') :
    ctx' = retainedContext ctx (neededFunctions ctx roots) := by
  unfold retainFunctions at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact (Except.ok.inj h).symm

/-- When `prepareTerms` succeeds with `p`, and assembling the context with the obligation's
definitions and declarations (`completeContext`) gives `assembled`, the assumptions and the goal
of `p` are the original ones normalized (`normalizeTerm`), every axiom of `p`'s context is an
axiom of `assembled` normalized, and every definition of `p`'s context is a definition of
`assembled` with its body normalized. -/
private theorem prepareTerms_eq
    {context : Core.SMT.Context} {assumptions : List Term} {goal : Term}
    {definitions : List Core.VarDefinition} {declarations : List Core.VarDeclaration}
    {assembled : Core.SMT.Context} {p : PreparedTerms}
    (hassembled : completeContext context definitions declarations = .ok assembled)
    (hprepared : prepareTerms context assumptions goal definitions declarations = .ok p) :
    p.assumptions = assumptions.map normalizeTerm ∧
    p.goal = normalizeTerm goal ∧
    (∀ a ∈ p.context.axms.toList, ∃ a₀ ∈ assembled.axms.toList, a = normalizeTerm a₀) ∧
    (∀ f ∈ p.context.ifs.toList,
      ∃ f₀ ∈ assembled.ifs.toList, f = { f₀ with body := normalizeTerm f₀.body }) := by
  unfold prepareTerms at hprepared
  simp only [bind, Except.bind, pure, Except.pure, hassembled] at hprepared
  split at hprepared
  · exact absurd hprepared (by simp)
  · rename_i pruned hpruned
    obtain rfl := retainFunctions_eq hpruned
    split at hprepared
    · exact absurd hprepared (by simp)
    · obtain rfl := Except.ok.inj hprepared
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro a ha
        obtain ⟨a₀, ha₀, rfl⟩ := mem_mapContextTerms_axms.mp ha
        exact ⟨a₀, ha₀, rfl⟩
      · intro f hf
        obtain ⟨f₀, hf₀, rfl⟩ := mem_mapContextTerms_ifs.mp hf
        exact ⟨f₀, mem_retainedContext_ifs hf₀, rfl⟩

/-! ## Normalization preserves denotations -/

/-! ### Shapes of normalized terms -/

section Shapes

/-- Normalization leaves a literal unchanged. -/
private theorem normalizeTerm_prim (p : TermPrim) : normalizeTerm (.prim p) = .prim p := by
  simp [normalizeTerm]
/-- Normalization leaves a variable unchanged. -/
private theorem normalizeTerm_var (v : TermVar) : normalizeTerm (.var v) = .var v := by
  simp [normalizeTerm]
/-- Normalization leaves the `Option` constant `none` unchanged. -/
private theorem normalizeTerm_none (ty : TermType) : normalizeTerm (.none ty) = .none ty := by
  simp [normalizeTerm]
/-- Normalization of `some t` normalizes `t` and keeps the `some`. -/
private theorem normalizeTerm_some (t : Term) :
    normalizeTerm (.some t) = .some (normalizeTerm t) := by
  simp [normalizeTerm]
/-- Normalization keeps a quantifier's kind and bound variables and normalizes its body and
every trigger term. -/
private theorem normalizeTerm_quant (q : QuantifierKind) (vs : List TermVar) (tr : List (List Term))
    (b : Term) :
    normalizeTerm (.quant q vs tr b)
      = .quant q vs (tr.map (List.map normalizeTerm)) (normalizeTerm b) := by
  simp [normalizeTerm]
/-- Normalization keeps an application of a declared or defined function and normalizes
its arguments. -/
private theorem normalizeTerm_uf (uf : UF) (args : List Term) (ty : TermType) :
    normalizeTerm (.app (.core (.uf uf)) args ty)
      = .app (.core (.uf uf)) (args.map normalizeTerm) ty := by
  simp [normalizeTerm]
/-- Normalization keeps `not` of one operand and normalizes the operand: it rewrites no `not`. -/
private theorem normalizeTerm_not (t : Term) (ty : TermType) :
    normalizeTerm (.app (.core .not) [t] ty) = .app (.core .not) [normalizeTerm t] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `and` and normalizes its operands: only `and` of fewer
than two operands is rewritten. -/
private theorem normalizeTerm_and (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.core .and) [t1, t2] ty)
      = .app (.core .and) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `or` and normalizes its operands: only `or` of fewer than
two operands is rewritten. -/
private theorem normalizeTerm_or (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.core .or) [t1, t2] ty)
      = .app (.core .or) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `=>` and normalizes its operands: it rewrites no `=>`. -/
private theorem normalizeTerm_implies (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.core .implies) [t1, t2] ty)
      = .app (.core .implies) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `=` and normalizes its operands: only a chain of three or
more operands is rewritten. -/
private theorem normalizeTerm_eq (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.core .eq) [t1, t2] ty)
      = .app (.core .eq) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps an `ite` of three operands and normalizes them: it rewrites no `ite`. -/
private theorem normalizeTerm_ite (c t e : Term) (ty : TermType) :
    normalizeTerm (.app (.core .ite) [c, t, e] ty)
      = .app (.core .ite) [normalizeTerm c, normalizeTerm t, normalizeTerm e] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a unary minus and normalizes its operand: it rewrites no negation. -/
private theorem normalizeTerm_neg (t : Term) (ty : TermType) :
    normalizeTerm (.app (.num .neg) [t] ty) = .app (.num .neg) [normalizeTerm t] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `+` and normalizes its operands: it rewrites no `+`. -/
private theorem normalizeTerm_add (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .add) [t1, t2] ty)
      = .app (.num .add) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `-` and normalizes its operands: it rewrites no `-`. -/
private theorem normalizeTerm_sub (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .sub) [t1, t2] ty)
      = .app (.num .sub) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `*` and normalizes its operands: it rewrites no `*`. -/
private theorem normalizeTerm_mul (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .mul) [t1, t2] ty)
      = .app (.num .mul) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `<=` and normalizes its operands: only a chain of three or
more operands is rewritten. -/
private theorem normalizeTerm_le (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .le) [t1, t2] ty)
      = .app (.num .le) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `<` and normalizes its operands: only a chain of three or
more operands is rewritten. -/
private theorem normalizeTerm_lt (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .lt) [t1, t2] ty)
      = .app (.num .lt) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `>=` and normalizes its operands: only a chain of three or
more operands is rewritten. -/
private theorem normalizeTerm_ge (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .ge) [t1, t2] ty)
      = .app (.num .ge) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary `>` and normalizes its operands: only a chain of three or
more operands is rewritten. -/
private theorem normalizeTerm_gt (t1 t2 : Term) (ty : TermType) :
    normalizeTerm (.app (.num .gt) [t1, t2] ty)
      = .app (.num .gt) [normalizeTerm t1, normalizeTerm t2] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary integer `div` and normalizes its operands: only `div` of
three or more operands is rewritten, into nested binary `div`s. -/
private theorem normalizeTerm_div (x y : Term) (ty : TermType) :
    normalizeTerm (.app (.num .div) [x, y] ty)
      = .app (.num .div) [normalizeTerm x, normalizeTerm y] ty := by
  simp [normalizeTerm]
/-- Normalization keeps a binary integer `mod` and normalizes its operands: it rewrites no
`mod`. -/
private theorem normalizeTerm_mod (x y : Term) (ty : TermType) :
    normalizeTerm (.app (.num .mod) [x, y] ty)
      = .app (.num .mod) [normalizeTerm x, normalizeTerm y] ty := by
  simp [normalizeTerm]
/-- Normalization keeps an array `select` of two operands and normalizes them: it rewrites
no `select`. -/
private theorem normalizeTerm_select (a i : Term) (ty : TermType) :
    normalizeTerm (.app .select [a, i] ty) =
      .app .select [normalizeTerm a, normalizeTerm i] ty := by
  simp [normalizeTerm]
/-- Normalization keeps an array `store` of three operands and normalizes them: it rewrites
no `store`. -/
private theorem normalizeTerm_store (a i e : Term) (ty : TermType) :
    normalizeTerm (.app .store [a, i, e] ty)
      = .app .store [normalizeTerm a, normalizeTerm i, normalizeTerm e] ty := by
  simp [normalizeTerm]

/-- `conjunction` of an empty list is the literal `true`. -/
private theorem conjunction_nil : conjunction [] = .prim (.bool true) := by
  simp [conjunction]

/-- `conjunction` of a single term is that term, with no `and` around it. -/
private theorem conjunction_single (t : Term) : conjunction [t] = t := by
  simp [conjunction]

/-- `conjunction` of two or more terms, a balanced tree of binary `and`s, is the `and` (of sort
`Bool`) of the conjunction of the first half of the terms, rounded down, and that of the rest. -/
private theorem conjunction_cons_cons (t u : Term) (rest : List Term) :
    conjunction (t :: u :: rest) =
      .app (.core .and) [conjunction ((t :: u :: rest).take ((rest.length + 2) / 2)),
        conjunction ((t :: u :: rest).drop ((rest.length + 2) / 2))] .bool := by
  rw [conjunction]

/-- Normalization turns `distinct` of two or more terms into `conjunction` (a balanced tree of
binary `and`s) of `not (x = y)` for each pair of operand positions, the operands normalized
first. -/
private theorem normalizeTerm_distinct (t1 t2 : Term) (ts : List Term) (ty : TermType) :
    normalizeTerm (.app (.core .distinct) (t1 :: t2 :: ts) ty)
      = conjunction (distinctPairs ((t1 :: t2 :: ts).map normalizeTerm)) := by
  simp only [normalizeTerm, List.map_cons]

end Shapes

/-- `conjunction` (a balanced tree of binary `and`s) of terms of sort `Bool` has sort `Bool`,
where a term's sort is the one written on it (`Term.typeOf`, read without type checking). -/
private theorem conjunction_typeOf (us : List Term) (h : ∀ u ∈ us, u.typeOf = .bool) :
    (conjunction us).typeOf = .bool := by
  match us with
  | [] => rw [conjunction_nil]; rfl
  | [t] => rw [conjunction_single]; exact h t List.mem_cons_self
  | t :: u :: rest => rw [conjunction_cons_cons]; rfl

/-- Every disequality `not (x = y)` that `distinctPairs` builds, one for each pair of positions
of the list, has sort `Bool` as written on the term (`Term.typeOf`). -/
private theorem distinctPairs_typeOf : ∀ (xs : List Term), ∀ u ∈ distinctPairs xs, u.typeOf = .bool
  | [], u, hu => by simp [distinctPairs] at hu
  | x :: rest, u, hu => by
    simp only [distinctPairs, List.mem_append, List.mem_map] at hu
    rcases hu with ⟨y, -, rfl⟩ | hu
    · rfl
    · exact distinctPairs_typeOf rest u hu

/-- A well-typed application is typed at its annotation. -/
private theorem typeOf_app {ctx : TypedContext} {op : Op} {args : List Term} {rty τ : TermType}
    (h : Term.typeCheck ctx (.app op args rty) = .ok τ) : rty = τ :=
  Term.typeOf_of_typeCheck h

/-- Normalization keeps the sort of a well-typed term: when `t` type-checks (`Term.typeCheck`)
at sort `τ`, the sort written on `normalizeTerm t` (`Term.typeOf`, read without type checking)
is `τ`. -/
private theorem typeOf_normalizeTerm {ctx : TypedContext} :
    ∀ {t : Term} {τ : TermType}, Term.typeCheck ctx t = .ok τ →
      (normalizeTerm t).typeOf = τ := by
  intro t τ h
  match t with
  | .prim p => rw [normalizeTerm_prim]; exact Term.typeOf_of_typeCheck h
  | .var v => rw [normalizeTerm_var]; exact Term.typeOf_of_typeCheck h
  | .none ty => rw [normalizeTerm_none]; exact Term.typeOf_of_typeCheck h
  | .some t1 =>
    obtain ⟨τ', h1, rfl⟩ := Term.typeCheck_some_inv h
    rw [normalizeTerm_some, Term.typeOf, typeOf_normalizeTerm h1]
  | .quant k vs tr body =>
    rw [normalizeTerm_quant, Term.typeOf]; exact (Term.typeCheck_quant_inv h).2.symm
  | .app (.core (.uf uf)) args rty => rw [normalizeTerm_uf]; exact typeOf_app h
  | .app (.core .not) [t1] rty => rw [normalizeTerm_not]; exact typeOf_app h
  | .app (.core .and) [t1, t2] rty => rw [normalizeTerm_and]; exact typeOf_app h
  | .app (.core .or) [t1, t2] rty => rw [normalizeTerm_or]; exact typeOf_app h
  | .app (.core .implies) [t1, t2] rty => rw [normalizeTerm_implies]; exact typeOf_app h
  | .app (.core .eq) [t1, t2] rty => rw [normalizeTerm_eq]; exact typeOf_app h
  | .app (.core .ite) [c, t1, e] rty => rw [normalizeTerm_ite]; exact typeOf_app h
  | .app (.num .neg) [t1] rty => rw [normalizeTerm_neg]; exact typeOf_app h
  | .app (.num .add) [t1, t2] rty => rw [normalizeTerm_add]; exact typeOf_app h
  | .app (.num .sub) [t1, t2] rty => rw [normalizeTerm_sub]; exact typeOf_app h
  | .app (.num .mul) [t1, t2] rty => rw [normalizeTerm_mul]; exact typeOf_app h
  | .app (.num .le) [t1, t2] rty => rw [normalizeTerm_le]; exact typeOf_app h
  | .app (.num .lt) [t1, t2] rty => rw [normalizeTerm_lt]; exact typeOf_app h
  | .app (.num .ge) [t1, t2] rty => rw [normalizeTerm_ge]; exact typeOf_app h
  | .app (.num .gt) [t1, t2] rty => rw [normalizeTerm_gt]; exact typeOf_app h
  | .app (.num .div) [t1, t2] rty => rw [normalizeTerm_div]; exact typeOf_app h
  | .app (.num .mod) [t1, t2] rty => rw [normalizeTerm_mod]; exact typeOf_app h
  | .app (.core .distinct) (t1 :: t2 :: ts) rty =>
    rw [normalizeTerm_distinct, conjunction_typeOf _ (distinctPairs_typeOf _)]
    exact (Term.typeCheck_distinct_inv h).2.2.2.symm
  | .app .select [a, i] rty => rw [normalizeTerm_select]; exact typeOf_app h
  | .app .store [a, i, e] rty => rw [normalizeTerm_store]; exact typeOf_app h
  | .app (.core .not) [] rty | .app (.core .not) (_ :: _ :: _) rty
  | .app (.core .and) [] rty | .app (.core .and) [_] rty | .app (.core .and) (_ :: _ :: _ :: _) rty
  | .app (.core .or) [] rty | .app (.core .or) [_] rty | .app (.core .or) (_ :: _ :: _ :: _) rty
  | .app (.core .implies) [] rty | .app (.core .implies) [_] rty
  | .app (.core .implies) (_ :: _ :: _ :: _) rty
  | .app (.core .eq) [] rty | .app (.core .eq) [_] rty | .app (.core .eq) (_ :: _ :: _ :: _) rty
  | .app (.core .ite) [] rty | .app (.core .ite) [_] rty | .app (.core .ite) [_, _] rty
  | .app (.core .ite) (_ :: _ :: _ :: _ :: _) rty
  | .app (.core .distinct) [] rty | .app (.core .distinct) [_] rty
  | .app (.num .neg) [] rty | .app (.num .neg) (_ :: _ :: _) rty
  | .app (.num .add) [] rty | .app (.num .add) [_] rty | .app (.num .add) (_ :: _ :: _ :: _) rty
  | .app (.num .sub) [] rty | .app (.num .sub) [_] rty | .app (.num .sub) (_ :: _ :: _ :: _) rty
  | .app (.num .mul) [] rty | .app (.num .mul) [_] rty | .app (.num .mul) (_ :: _ :: _ :: _) rty
  | .app (.num .div) [] rty | .app (.num .div) [_] rty | .app (.num .div) (_ :: _ :: _ :: _) rty
  | .app (.num .mod) [] rty | .app (.num .mod) [_] rty | .app (.num .mod) (_ :: _ :: _ :: _) rty
  | .app (.num .le) [] rty | .app (.num .le) [_] rty | .app (.num .le) (_ :: _ :: _ :: _) rty
  | .app (.num .lt) [] rty | .app (.num .lt) [_] rty | .app (.num .lt) (_ :: _ :: _ :: _) rty
  | .app (.num .ge) [] rty | .app (.num .ge) [_] rty | .app (.num .ge) (_ :: _ :: _ :: _) rty
  | .app (.num .gt) [] rty | .app (.num .gt) [_] rty | .app (.num .gt) (_ :: _ :: _ :: _) rty
  | .app .select [] rty | .app .select [_] rty | .app .select (_ :: _ :: _ :: _) rty
  | .app .store [] rty | .app .store [_] rty | .app .store [_, _] rty
  | .app .store (_ :: _ :: _ :: _ :: _) rty
  | .app (.num .rdiv) _ rty | .app (.num .abs) _ rty
  | .app (.bv _) _ rty | .app (.str _) _ rty
  | .app .option_get _ rty | .app (.datatype_op _ _) _ rty =>
    simp [Term.typeCheck] at h

/-! ### Denotations -/

/-- Inversion for a well-typed application of a function symbol: if `uf` applied to `args`
type-checks to `τ`, then `uf` is in the context's function list, the arguments type-check one by
one to `uf`'s argument sorts, and `τ` is `uf`'s result sort. -/
private theorem typeCheck_uf_inv {ctx : TypedContext} {uf : UF} {args : List Term}
    {rty τ : TermType}
    (h : Term.typeCheck ctx (.app (.core (.uf uf)) args rty) = .ok τ) :
    uf ∈ ctx.ufs ∧ Term.typeCheckArgs ctx args uf.args = true ∧ τ = uf.out := by
  simp only [Term.typeCheck] at h
  split at h <;> (try split at h) <;> simp_all

section Denotations
variable {σ : SortInterp} {𝒜 : ArrayTheory}

/-- The value of a well-typed array read `select a i`, for any array theory `𝒜` (entailment
quantifies over all of them): `𝒜.select` applied to the value of `a` at its sort `Array k v` and
the value of `i` at the key sort `k`, cast to the term's type `τ` (which is `v`), where `k` and
`v` are the sorts type checking gives `a`. -/
private theorem denoteTyped_select' {ctx : TypedContext} (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) (a i : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app .select [a, i] rty) = .ok τ) :
    Term.denoteTyped I env dz mz (.app .select [a, i] rty) τ htc
      = cast (congrArg (TermType.denoteTyped σ 𝒜) (Term.typeCheck_select_inv htc).2.2.2.2.2.symm)
          (𝒜.select
            (Term.denoteTyped I env dz mz a
              (.constr "Array" [(Term.typeCheck_select_inv htc).1,
                (Term.typeCheck_select_inv htc).2.1])
              (Term.typeCheck_select_inv htc).2.2.1)
            (Term.denoteTyped I env dz mz i (Term.typeCheck_select_inv htc).1
              (Term.typeCheck_select_inv htc).2.2.2.1)) := by
  simp only [Term.denoteTyped]

/-- The value of a well-typed array write `store a i e`, for any array theory `𝒜` (entailment
quantifies over all of them): `𝒜.store` applied to the values of `a` at its sort `Array k v`, of
`i` at the key sort `k` and of `e` at the value sort `v`, cast to the term's type `τ` (which is
`Array k v`), where `k` and `v` are the sorts type checking gives `a`. -/
private theorem denoteTyped_store' {ctx : TypedContext} (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) (a i e : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app .store [a, i, e] rty) = .ok τ) :
    Term.denoteTyped I env dz mz (.app .store [a, i, e] rty) τ htc
      = cast (congrArg (TermType.denoteTyped σ 𝒜) (Term.typeCheck_store_inv htc).2.2.2.2.2.2.symm)
          (𝒜.store
            (Term.denoteTyped I env dz mz a
              (.constr "Array" [(Term.typeCheck_store_inv htc).1,
                (Term.typeCheck_store_inv htc).2.1])
              (Term.typeCheck_store_inv htc).2.2.1)
            (Term.denoteTyped I env dz mz i (Term.typeCheck_store_inv htc).1
              (Term.typeCheck_store_inv htc).2.2.2.1)
            (Term.denoteTyped I env dz mz e (Term.typeCheck_store_inv htc).2.1
              (Term.typeCheck_store_inv htc).2.2.2.2.1)) := by
  simp only [Term.denoteTyped]

/-- The value of `t` at sort `ty`, or `default` when `t` is not typed at `ty`. -/
noncomputable def valueAt [SortInterp.AllInhabited σ] (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) (ctx : TypedContext) (ty : TermType) (t : Term) :
    TermType.denoteTyped σ 𝒜 ty :=
  if h : Term.typeCheck ctx t = .ok ty then Term.denoteTyped I env dz mz t ty h else default

/-- On a term that type-checks to `ty`, `valueAt` (the value of a term at a sort, or `default`
when the term does not have that sort) is the term's typed denotation at `ty`. -/
private theorem valueAt_eq [SortInterp.AllInhabited σ] (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) {ctx : TypedContext} {ty : TermType} {t : Term}
    (h : Term.typeCheck ctx t = .ok ty) :
    valueAt I env dz mz ctx ty t = Term.denoteTyped I env dz mz t ty h := by
  unfold valueAt; rw [dite_eq_left h]

/-- For a list of `n` terms that type-check as arguments against `n` copies of the sort `ty`,
flattening the heterogeneous list of their typed denotations into a plain list
(`hlistReplicateToList`) gives their values at `ty`, term by term (`valueAt`). -/
private theorem hlistReplicateToList_denoteTypedArgs [SortInterp.AllInhabited σ] (I : UFInterp σ 𝒜)
    (env : VarEnv σ 𝒜) (dz mz : Int → Int) {ctx : TypedContext} (ty : TermType) :
    ∀ (args : List Term) (n : Nat) (h : Term.typeCheckArgs ctx args (List.replicate n ty) = true),
      hlistReplicateToList n (Term.denoteTypedArgs I env dz mz args (List.replicate n ty) h)
        = args.map (valueAt I env dz mz ctx ty)
  | [], 0, _ => rfl
  | [], _ + 1, h => by simp [Term.typeCheckArgs, List.replicate_succ] at h
  | _ :: _, 0, h => by simp [Term.typeCheckArgs] at h
  | t :: ts, n + 1, h => by
    have ht : Term.typeCheck ctx t = .ok ty := by
      simp only [List.replicate_succ, Term.typeCheckArgs] at h
      split at h <;> simp_all
    have hts : Term.typeCheckArgs ctx ts (List.replicate n ty) = true := by
      simp only [List.replicate_succ, Term.typeCheckArgs] at h
      split at h <;> simp_all
    show hlistReplicateToList (n + 1)
        (Term.denoteTypedArgs I env dz mz (t :: ts) (ty :: List.replicate n ty) h) = _
    simp only [Term.denoteTypedArgs, hlistReplicateToList, List.map_cons]
    rw [hlistReplicateToList_denoteTypedArgs I env dz mz ty ts n hts, valueAt_eq I env dz mz ht]

/-- If `conjunction us` (the balanced tree of binary `and`s over `us`) type-checks to `Bool`, so
does every term of `us`. -/
private theorem conjunction_typeCheck {ctx : TypedContext} :
    ∀ (us : List Term), Term.typeCheck ctx (conjunction us) = .ok .bool →
      ∀ u ∈ us, Term.typeCheck ctx u = .ok .bool
  | [], _, _, hu => absurd hu (List.not_mem_nil)
  | [t], h, w, hw => by
    rw [List.mem_singleton.mp hw]
    rwa [conjunction_single] at h
  | t :: u :: rest, h, w, hw => by
    rw [conjunction_cons_cons] at h
    obtain ⟨hl, hr, -⟩ := Term.typeCheck_boolBin_inv (op := .and) h (.inl rfl)
    rw [← List.take_append_drop ((rest.length + 2) / 2) (t :: u :: rest)] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact conjunction_typeCheck _ hl w hw
    · exact conjunction_typeCheck _ hr w hw
termination_by us => us.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- Equal terms denote the same value. -/
private theorem denoteTyped_of_eq (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    {ctx : TypedContext} {t t' : Term} {τ : TermType} (e : t = t')
    (h : Term.typeCheck ctx t = .ok τ) :
    Term.denoteTyped I env dz mz t τ h = Term.denoteTyped I env dz mz t' τ (e ▸ h) := by
  subst e; rfl

/-- If `conjunction us` (the balanced tree of binary `and`s over `us`, `true` when `us` is empty)
type-checks to `Bool`, it denotes `true` iff every term of `us` does. -/
private theorem denote_conjunction_iff (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    {ctx : TypedContext} :
    ∀ (us : List Term) (h : Term.typeCheck ctx (conjunction us) = .ok .bool),
      Term.denoteTyped I env dz mz (conjunction us) .bool h = true ↔
        ∀ u (hu : u ∈ us),
          Term.denoteTyped I env dz mz u .bool (conjunction_typeCheck us h u hu) = true
  | [], h => by
    rw [denoteTyped_of_eq I env dz mz conjunction_nil h]
    constructor
    · intro _ u hu; exact absurd hu List.not_mem_nil
    · intro _
      simp only [Term.denoteTyped]
  | [t], h => by
    rw [denoteTyped_of_eq I env dz mz (conjunction_single t) h]
    constructor
    · intro H u hu
      obtain rfl := List.mem_singleton.mp hu
      exact H
    · intro H
      exact H t List.mem_cons_self
  | t :: u :: rest, h => by
    rw [denoteTyped_of_eq I env dz mz (conjunction_cons_cons t u rest) h]
    have h' := (conjunction_cons_cons t u rest) ▸ h
    rw [Term.denoteTyped_and I env dz mz _ _ .bool .bool h']
    simp only [cast_eq, Bool.and_eq_true]
    rw [denote_conjunction_iff I env dz mz _ (Term.typeCheck_boolBin_inv h' (.inl rfl)).1,
      denote_conjunction_iff I env dz mz _ (Term.typeCheck_boolBin_inv h' (.inl rfl)).2.1]
    constructor
    · rintro ⟨h1, h2⟩ w hw
      have hw' := hw
      rw [← List.take_append_drop ((rest.length + 2) / 2) (t :: u :: rest)] at hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · exact h1 w hw'
      · exact h2 w hw'
    · intro H
      exact ⟨fun w hw => H w (List.mem_of_mem_take hw), fun w hw => H w (List.mem_of_mem_drop hw)⟩
termination_by us => us.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- Let `v` give each term a value, and let `P` be a property of terms that holds of a disequality
`¬(x = y)` between elements of `xs` exactly when `v x ≠ v y`. Then `P` holds of every
disequality in `distinctPairs xs` (one for each pair of positions in `xs`) iff the values of the
elements of `xs` are pairwise different. -/
private theorem distinctPairs_iff_pairwise {α : Type} (v : Term → α) (P : Term → Prop) :
    ∀ (xs : List Term),
      (∀ x ∈ xs, ∀ y ∈ xs,
        P (.app (.core .not) [.app (.core .eq) [x, y] .bool] .bool) ↔ v x ≠ v y) →
      ((∀ u ∈ distinctPairs xs, P u) ↔ (xs.map v).Pairwise (· ≠ ·))
  | [], _ => by simp [distinctPairs]
  | x :: xs, hP => by
    simp only [distinctPairs, List.mem_append, List.map_cons, List.pairwise_cons, List.mem_map]
    rw [← distinctPairs_iff_pairwise v P xs
      (fun a ha b hb => hP a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))]
    constructor
    · intro H
      refine ⟨?_, fun u hu => H u (Or.inr hu)⟩
      rintro _ ⟨y, hy, rfl⟩
      exact (hP x List.mem_cons_self y (List.mem_cons_of_mem x hy)).mp (H _ (Or.inl ⟨y, hy, rfl⟩))
    · rintro ⟨H1, H2⟩ u hu
      rcases hu with ⟨y, hy, rfl⟩ | hu
      · exact (hP x List.mem_cons_self y (List.mem_cons_of_mem x hy)).mpr (H1 _ ⟨y, hy, rfl⟩)
      · exact H2 u hu

/-- A well-typed `distinct` of two or more terms denotes whether the values of its operands at
their common sort `ty` (the sort type checking gives the first operand), computed with
`valueAt`, are pairwise different. -/
private theorem denoteTyped_distinct' [SortInterp.AllInhabited σ] (I : UFInterp σ 𝒜)
    (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) {ctx : TypedContext} (t1 t2 : Term) (ts : List Term) (rty : TermType)
    (htc : Term.typeCheck ctx (.app (.core .distinct) (t1 :: t2 :: ts) rty) = .ok .bool)
    (ty : TermType) (hty : (Term.typeCheck_distinct_inv htc).1 = ty) :
    Term.denoteTyped I env dz mz (.app (.core .distinct) (t1 :: t2 :: ts) rty) .bool htc
      = decide (((t1 :: t2 :: ts).map (valueAt I env dz mz ctx ty)).Pairwise (· ≠ ·)) := by
  simp only [Term.denoteTyped]
  rcases hd : Term.typeCheck_distinct_inv htc with ⟨ty', ht, hts, heq⟩
  rw [hd] at hty
  simp only at hty
  subst ty'
  simp only [cast_eq]
  have hargs : Term.typeCheckArgs ctx (t1 :: t2 :: ts)
      (List.replicate (t1 :: t2 :: ts).length ty) = true := by
    show Term.typeCheckArgs ctx (t1 :: t2 :: ts) (ty :: List.replicate (t2 :: ts).length ty) = true
    simp only [Term.typeCheckArgs, ht, BEq.beq, decide_eq_true_eq, hts, Bool.and_true]
  rw [hlistReplicateToList_denoteTypedArgs I env dz mz ty (t1 :: t2 :: ts) _ hargs]
  exact decide_eq_decide.mpr Iff.rfl

/-- If a list of terms type-checks as arguments against as many copies of the sort `ty` as it has
terms, every term of the list type-checks to `ty`. -/
private theorem typeCheckArgs_replicate_mem {ctx : TypedContext} {ty : TermType} :
    ∀ {args : List Term}, Term.typeCheckArgs ctx args (List.replicate args.length ty) = true →
      ∀ u ∈ args, Term.typeCheck ctx u = .ok ty
  | [], _, _, hu => absurd hu List.not_mem_nil
  | t :: ts, h, u, hu => by
    simp only [List.length_cons, List.replicate_succ, Term.typeCheckArgs] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · split at h <;> simp_all
    · split at h
      · simp only [Bool.and_eq_true] at h
        exact typeCheckArgs_replicate_mem h.2 u hu
      · simp at h

/-- If every term of a list type-checks to `ty`, the list type-checks as arguments against as many
copies of `ty` as it has terms. -/
private theorem typeCheckArgs_replicate_of_mem {ctx : TypedContext} {ty : TermType} :
    ∀ {args : List Term}, (∀ u ∈ args, Term.typeCheck ctx u = .ok ty) →
      Term.typeCheckArgs ctx args (List.replicate args.length ty) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.length_cons, List.replicate_succ, Term.typeCheckArgs, h t List.mem_cons_self,
      BEq.rfl, Bool.true_and]
    exact typeCheckArgs_replicate_of_mem fun u hu => h u (List.mem_cons_of_mem t hu)

/-- In a list of two or more terms, every element `u` occurs in one of the disequalities that
`distinctPairs` builds for the list (one `¬(x = y)` for each pair of positions): for some element
`w` of the list, `¬(u = w)` or `¬(w = u)` is among them. -/
private theorem mem_distinctPairs_of_mem {x y : Term} {rest : List Term} {u : Term}
    (hu : u ∈ x :: y :: rest) :
    ∃ w ∈ x :: y :: rest,
      (.app (.core .not) [.app (.core .eq) [u, w] .bool] .bool) ∈ distinctPairs (x :: y :: rest) ∨
      (.app (.core .not) [.app (.core .eq) [w, u] .bool] .bool) ∈
        distinctPairs (x :: y :: rest) := by
  simp only [distinctPairs, List.mem_append, List.mem_map]
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ⟨y, List.mem_cons_of_mem u List.mem_cons_self,
      Or.inl (Or.inl ⟨y, List.mem_cons_self, rfl⟩)⟩
  · exact ⟨x, List.mem_cons_self, Or.inr (Or.inl ⟨u, hu, rfl⟩)⟩

/-- The disequality `¬(a = b)` of two terms of the same sort type-checks to `Bool`. -/
private theorem pair_typeCheck {ctx : TypedContext} {a b : Term} {ty : TermType}
    (ha : Term.typeCheck ctx a = .ok ty) (hb : Term.typeCheck ctx b = .ok ty) :
    Term.typeCheck ctx (.app (.core .not) [.app (.core .eq) [a, b] .bool] .bool) = .ok .bool := by
  simp [Term.typeCheck, ha, hb, bind, Except.bind]

/-- For two terms `a` and `b` of the same sort `ty`, the disequality `¬(a = b)` denotes `true` iff
the values of `a` and `b` at `ty` (computed with `valueAt`) differ. -/
private theorem denote_pair_iff [SortInterp.AllInhabited σ] (I : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (dz mz : Int → Int) {ctx : TypedContext} {a b : Term} {ty : TermType}
    (ha : Term.typeCheck ctx a = .ok ty) (hb : Term.typeCheck ctx b = .ok ty)
    (h : Term.typeCheck ctx (.app (.core .not) [.app (.core .eq) [a, b] .bool] .bool) = .ok .bool) :
    Term.denoteTyped I env dz mz (.app (.core .not) [.app (.core .eq) [a, b] .bool] .bool) .bool h
        = true ↔
      valueAt I env dz mz ctx ty a ≠ valueAt I env dz mz ctx ty b := by
  rw [Term.denoteTyped_not I env dz mz _ .bool .bool h]
  simp only [cast_eq]
  rw [Term.denoteTyped_eq I env dz mz a b .bool .bool (Term.typeCheck_not_inv h).1]
  rcases hs : Term.typeCheck_eq_inv (Term.typeCheck_not_inv h).1 with ⟨τ', q1, q2, -⟩
  have hτ : τ' = ty := (Term.typeOf_of_typeCheck q1).symm.trans (Term.typeOf_of_typeCheck ha)
  subst hτ
  simp only [cast_eq]
  rw [valueAt_eq I env dz mz ha, valueAt_eq I env dz mz hb]
  simp

end Denotations

mutual
/-- Normalization preserves values: if a term `t` type-checks to `τ` in a typing context `ctx` and
`normalizeTerm t` type-checks to `τ` in a typing context `ctx'`, the two denote the same value
under the same interpretation of the functions, variable environment and completions of division
and modulo by zero. The typing in `ctx'` is a hypothesis because the two contexts may differ. By
induction on `t`. -/
private theorem denote_normalizeTerm {σ : SortInterp} {𝒜 : ArrayTheory} [SortInterp.AllInhabited σ]
    (I : UFInterp σ 𝒜) (dz mz : Int → Int) {ctx ctx' : TypedContext}
    (env : VarEnv σ 𝒜) (t : Term) (τ : TermType) (h : Term.typeCheck ctx t = .ok τ)
    (t' : Term) (ht' : t' = normalizeTerm t) (h' : Term.typeCheck ctx' t' = .ok τ) :
    Term.denoteTyped I env dz mz t' τ h' = Term.denoteTyped I env dz mz t τ h := by
  match t with
  | .prim p =>
    rw [normalizeTerm_prim] at ht'; subst ht'
    simp only [Term.denoteTyped]
    cases p <;> rfl
  | .var v =>
    rw [normalizeTerm_var] at ht'; subst ht'
    simp only [Term.denoteTyped]
  | .none ty =>
    rw [normalizeTerm_none] at ht'; subst ht'
    simp only [Term.denoteTyped]
  | .some t1 =>
    rw [normalizeTerm_some] at ht'; subst ht'
    rw [Term.denoteTyped_some I env dz mz t1 τ h, Term.denoteTyped_some I env dz mz _ τ h']
    rcases hs : Term.typeCheck_some_inv h with ⟨a, q, e⟩
    rcases hs' : Term.typeCheck_some_inv h' with ⟨a', q', e'⟩
    subst e
    have hea : a' = a := by injection e' with hea; exact hea.symm
    subst hea
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 a' q _ rfl q']
  | .quant k vs tr body =>
    rw [normalizeTerm_quant] at ht'; subst ht'
    obtain ⟨hb, heq⟩ := Term.typeCheck_quant_inv h
    obtain ⟨hb', -⟩ := Term.typeCheck_quant_inv h'
    subst heq
    rw [Term.denoteTyped_quant_eq I env dz mz k vs tr body h hb,
      Term.denoteTyped_quant_eq I env dz mz k vs _ _ h' hb']
    apply decide_eq_decide.mpr
    cases k
    · exact forall_congr' fun ext => by
        rw [denote_normalizeTerm (ctx := { ctx with Γ := vs.reverse ++ ctx.Γ })
          (ctx' := { ctx' with Γ := vs.reverse ++ ctx'.Γ }) I dz mz _ body .bool hb _ rfl hb']
    · exact exists_congr fun ext => by
        rw [denote_normalizeTerm (ctx := { ctx with Γ := vs.reverse ++ ctx.Γ })
          (ctx' := { ctx' with Γ := vs.reverse ++ ctx'.Γ }) I dz mz _ body .bool hb _ rfl hb']
  | .app (.core (.uf uf)) args rty =>
    rw [normalizeTerm_uf] at ht'; subst ht'
    obtain ⟨-, hargs, heq⟩ := typeCheck_uf_inv h
    obtain ⟨-, hargs', -⟩ := typeCheck_uf_inv h'
    subst heq
    rw [Term.denoteTyped_uf I env dz mz uf args rty uf.out h hargs rfl,
      Term.denoteTyped_uf I env dz mz uf _ rty uf.out h' hargs' rfl]
    simp only [cast_eq]
    rw [denoteArgs_normalizeTerm I dz mz env args uf.args hargs _ rfl hargs']
  | .app (.core .not) [t1] rty =>
    rw [normalizeTerm_not] at ht'; subst ht'
    obtain ⟨-, heq⟩ := Term.typeCheck_not_inv h
    subst heq
    rw [Term.denoteTyped_not I env dz mz t1 rty .bool h,
      Term.denoteTyped_not I env dz mz _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .bool
      (Term.typeCheck_not_inv h).1 _ rfl (Term.typeCheck_not_inv h').1]
  | .app (.core .and) [t1, t2] rty =>
    rw [normalizeTerm_and] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_boolBin_inv h (.inl rfl)
    subst heq
    rw [Term.denoteTyped_and I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_and I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .bool
        (Term.typeCheck_boolBin_inv h (.inl rfl)).1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inl rfl)).1,
      denote_normalizeTerm I dz mz env t2 .bool
        (Term.typeCheck_boolBin_inv h (.inl rfl)).2.1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inl rfl)).2.1]
  | .app (.core .or) [t1, t2] rty =>
    rw [normalizeTerm_or] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inl rfl))
    subst heq
    rw [Term.denoteTyped_or I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_or I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .bool
        (Term.typeCheck_boolBin_inv h (.inr (.inl rfl))).1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inr (.inl rfl))).1,
      denote_normalizeTerm I dz mz env t2 .bool
        (Term.typeCheck_boolBin_inv h (.inr (.inl rfl))).2.1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inr (.inl rfl))).2.1]
  | .app (.core .implies) [t1, t2] rty =>
    rw [normalizeTerm_implies] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_boolBin_inv h (.inr (.inr rfl))
    subst heq
    rw [Term.denoteTyped_implies I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_implies I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .bool
        (Term.typeCheck_boolBin_inv h (.inr (.inr rfl))).1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inr (.inr rfl))).1,
      denote_normalizeTerm I dz mz env t2 .bool
        (Term.typeCheck_boolBin_inv h (.inr (.inr rfl))).2.1 _ rfl
        (Term.typeCheck_boolBin_inv h' (.inr (.inr rfl))).2.1]
  | .app (.core .eq) [t1, t2] rty =>
    rw [normalizeTerm_eq] at ht'; subst ht'
    rw [Term.denoteTyped_eq I env dz mz t1 t2 rty τ h,
      Term.denoteTyped_eq I env dz mz _ _ rty τ h']
    rcases hs : Term.typeCheck_eq_inv h with ⟨a, q1, q2, e⟩
    rcases hs' : Term.typeCheck_eq_inv h' with ⟨a', q1', q2', e'⟩
    subst e
    have hea : a' = a :=
      (Term.typeOf_of_typeCheck q1').symm.trans (typeOf_normalizeTerm q1)
    subst hea
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 a' q1 _ rfl q1',
      denote_normalizeTerm I dz mz env t2 a' q2 _ rfl q2']
  | .app (.core .ite) [c, t1, e] rty =>
    rw [normalizeTerm_ite] at ht'; subst ht'
    rw [Term.denoteTyped_ite I env dz mz c t1 e rty τ h,
      Term.denoteTyped_ite I env dz mz _ _ _ rty τ h']
    rw [denote_normalizeTerm I dz mz env c .bool
        (Term.typeCheck_ite_inv h).1 _ rfl (Term.typeCheck_ite_inv h').1,
      denote_normalizeTerm I dz mz env t1 τ
        (Term.typeCheck_ite_inv h).2.1 _ rfl (Term.typeCheck_ite_inv h').2.1,
      denote_normalizeTerm I dz mz env e τ
        (Term.typeCheck_ite_inv h).2.2 _ rfl (Term.typeCheck_ite_inv h').2.2]
  | .app (.num .neg) [t1] rty =>
    rw [normalizeTerm_neg] at ht'; subst ht'
    obtain ⟨-, heq⟩ := Term.typeCheck_intUn_inv h
    subst heq
    rw [Term.denoteTyped_neg I env dz mz t1 rty .int h,
      Term.denoteTyped_neg I env dz mz _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
      (Term.typeCheck_intUn_inv h).1 _ rfl (Term.typeCheck_intUn_inv h').1]
  | .app (.num .add) [t1, t2] rty =>
    rw [normalizeTerm_add] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intBin_inv h (.inl rfl)
    subst heq
    rw [Term.denoteTyped_add I env dz mz t1 t2 rty .int h,
      Term.denoteTyped_add I env dz mz _ _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intBin_inv h (.inl rfl)).1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inl rfl)).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intBin_inv h (.inl rfl)).2.1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inl rfl)).2.1]
  | .app (.num .sub) [t1, t2] rty =>
    rw [normalizeTerm_sub] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inl rfl))
    subst heq
    rw [Term.denoteTyped_sub I env dz mz t1 t2 rty .int h,
      Term.denoteTyped_sub I env dz mz _ _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intBin_inv h (.inr (.inl rfl))).1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inl rfl))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intBin_inv h (.inr (.inl rfl))).2.1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inl rfl))).2.1]
  | .app (.num .mul) [t1, t2] rty =>
    rw [normalizeTerm_mul] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inl rfl)))
    subst heq
    rw [Term.denoteTyped_mul I env dz mz t1 t2 rty .int h,
      Term.denoteTyped_mul I env dz mz _ _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inl rfl)))).1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inl rfl)))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inl rfl)))).2.1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inl rfl)))).2.1]
  | .app (.num .le) [t1, t2] rty =>
    rw [normalizeTerm_le] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intCmp_inv h (.inl rfl)
    subst heq
    rw [Term.denoteTyped_le I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_le I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intCmp_inv h (.inl rfl)).1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inl rfl)).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intCmp_inv h (.inl rfl)).2.1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inl rfl)).2.1]
  | .app (.num .lt) [t1, t2] rty =>
    rw [normalizeTerm_lt] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inl rfl))
    subst heq
    rw [Term.denoteTyped_lt I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_lt I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inl rfl))).1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inl rfl))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inl rfl))).2.1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inl rfl))).2.1]
  | .app (.num .ge) [t1, t2] rty =>
    rw [normalizeTerm_ge] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inl rfl)))
    subst heq
    rw [Term.denoteTyped_ge I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_ge I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inr (.inl rfl)))).1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inr (.inl rfl)))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inr (.inl rfl)))).2.1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inr (.inl rfl)))).2.1]
  | .app (.num .gt) [t1, t2] rty =>
    rw [normalizeTerm_gt] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intCmp_inv h (.inr (.inr (.inr rfl)))
    subst heq
    rw [Term.denoteTyped_gt I env dz mz t1 t2 rty .bool h,
      Term.denoteTyped_gt I env dz mz _ _ rty .bool h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inr (.inr rfl)))).1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inr (.inr rfl)))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intCmp_inv h (.inr (.inr (.inr rfl)))).2.1 _ rfl
        (Term.typeCheck_intCmp_inv h' (.inr (.inr (.inr rfl)))).2.1]
  | .app (.num .div) [t1, t2] rty =>
    rw [normalizeTerm_div] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inl rfl))))
    subst heq
    rw [Term.denoteTyped_div I env dz mz t1 t2 rty .int h,
      Term.denoteTyped_div I env dz mz _ _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inl rfl))))).1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inr (.inl rfl))))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inl rfl))))).2.1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inr (.inl rfl))))).2.1]
  | .app (.num .mod) [t1, t2] rty =>
    rw [normalizeTerm_mod] at ht'; subst ht'
    obtain ⟨-, -, heq⟩ := Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inr rfl))))
    subst heq
    rw [Term.denoteTyped_mod I env dz mz t1 t2 rty .int h,
      Term.denoteTyped_mod I env dz mz _ _ rty .int h']
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env t1 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inr rfl))))).1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inr (.inr rfl))))).1,
      denote_normalizeTerm I dz mz env t2 .int
        (Term.typeCheck_intBin_inv h (.inr (.inr (.inr (.inr rfl))))).2.1 _ rfl
        (Term.typeCheck_intBin_inv h' (.inr (.inr (.inr (.inr rfl))))).2.1]
  | .app (.core .distinct) (t1 :: t2 :: ts) rty =>
    rw [normalizeTerm_distinct] at ht'; subst ht'
    have heq : τ = .bool := (Term.typeCheck_distinct_inv h).2.2.2
    subst heq
    rw [denoteTyped_distinct' I env dz mz t1 t2 ts rty h _ rfl]
    generalize hty : (Term.typeCheck_distinct_inv h).1 = ty
    have hargsTy : ∀ u ∈ t1 :: t2 :: ts, Term.typeCheck ctx u = .ok ty := by
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · rw [← hty]; exact (Term.typeCheck_distinct_inv h).2.1
      · have hts := (Term.typeCheck_distinct_inv h).2.2.1
        rw [hty] at hts
        exact typeCheckArgs_replicate_mem hts u hu
    have hpairTy := conjunction_typeCheck _ h'
    -- every normalized element is typed at `ty`, because it occurs in a pair
    have hTTy : ∀ u ∈ t1 :: t2 :: ts, Term.typeCheck ctx' (normalizeTerm u) = .ok ty := by
      intro u hu
      have hu' : normalizeTerm u ∈
          normalizeTerm t1 :: normalizeTerm t2 :: ts.map normalizeTerm :=
        List.mem_map_of_mem hu
      obtain ⟨w, -, hp | hp⟩ := mem_distinctPairs_of_mem hu'
      · obtain ⟨h1, -⟩ := Term.typeCheck_not_inv (hpairTy _ hp)
        obtain ⟨a, q1, -, -⟩ := Term.typeCheck_eq_inv h1
        have : a = ty :=
          (Term.typeOf_of_typeCheck q1).symm.trans (typeOf_normalizeTerm (hargsTy u hu))
        rw [← this]; exact q1
      · obtain ⟨h1, -⟩ := Term.typeCheck_not_inv (hpairTy _ hp)
        obtain ⟨a, -, q2, -⟩ := Term.typeCheck_eq_inv h1
        have : a = ty :=
          (Term.typeOf_of_typeCheck q2).symm.trans (typeOf_normalizeTerm (hargsTy u hu))
        rw [← this]; exact q2
    apply Bool.eq_iff_iff.mpr
    rw [denote_conjunction_iff I env dz mz _ h', decide_eq_true_iff]
    have key : (∀ u (hu : u ∈ distinctPairs ((t1 :: t2 :: ts).map normalizeTerm)),
        Term.denoteTyped I env dz mz u .bool (conjunction_typeCheck _ h' u hu) = true) ↔
        (∀ u ∈ distinctPairs ((t1 :: t2 :: ts).map normalizeTerm),
          ∀ hu : Term.typeCheck ctx' u = .ok .bool,
            Term.denoteTyped I env dz mz u .bool hu = true) :=
      ⟨fun H u hu _ => H u hu, fun H u hu => H u hu _⟩
    rw [key, distinctPairs_iff_pairwise (valueAt I env dz mz ctx' ty) _ _ (by
      intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
      constructor
      · intro H
        exact (denote_pair_iff I env dz mz (hTTy a₀ ha₀) (hTTy b₀ hb₀)
          (pair_typeCheck (hTTy a₀ ha₀) (hTTy b₀ hb₀))).mp (H _)
      · intro H hu
        exact (denote_pair_iff I env dz mz (hTTy a₀ ha₀) (hTTy b₀ hb₀) hu).mpr H)]
    -- the two value lists agree, by the argument lemma
    have hargs : Term.typeCheckArgs ctx (t1 :: t2 :: ts)
        (List.replicate (t1 :: t2 :: ts).length ty) = true :=
      typeCheckArgs_replicate_of_mem hargsTy
    have hargs' : Term.typeCheckArgs ctx' ((t1 :: t2 :: ts).map normalizeTerm)
        (List.replicate (t1 :: t2 :: ts).length ty) = true := by
      have := typeCheckArgs_replicate_of_mem (ctx := ctx') (ty := ty)
        (args := (t1 :: t2 :: ts).map normalizeTerm) (by
          intro u hu
          obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp hu
          exact hTTy u₀ hu₀)
      simpa only [List.length_map] using this
    have hvals := denoteArgs_normalizeTerm I dz mz env (t1 :: t2 :: ts)
      (List.replicate (t1 :: t2 :: ts).length ty) hargs _ rfl hargs'
    have hl := congrArg (hlistReplicateToList (t1 :: t2 :: ts).length) hvals
    rw [hlistReplicateToList_denoteTypedArgs I env dz mz ty (t1 :: t2 :: ts) _ hargs,
      hlistReplicateToList_denoteTypedArgs I env dz mz ty _ _ hargs'] at hl
    rw [hl]
  | .app .select [a, i] rty =>
    rw [normalizeTerm_select] at ht'; subst ht'
    rw [denoteTyped_select' I env dz mz a i rty τ h, denoteTyped_select' I env dz mz _ _ rty τ h']
    rcases hs : Term.typeCheck_select_inv h with ⟨k, v, ha, hi, hrty, e⟩
    rcases hs' : Term.typeCheck_select_inv h' with ⟨k', v', ha', hi', hrty', e'⟩
    subst τ
    have hk : k' = k := by
      have hArray := (Term.typeOf_of_typeCheck ha').symm.trans (typeOf_normalizeTerm ha)
      injection hArray with _ hSorts
      injection hSorts with hk
    have hv : v' = v := by
      have hArray := (Term.typeOf_of_typeCheck ha').symm.trans (typeOf_normalizeTerm ha)
      injection hArray with _ hSorts
      injection hSorts with _ hValue
      injection hValue with hv
    subst hk hv
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env a _ ha _ rfl ha',
      denote_normalizeTerm I dz mz env i _ hi _ rfl hi']
  | .app .store [a, i, e] rty =>
    rw [normalizeTerm_store] at ht'; subst ht'
    rw [denoteTyped_store' I env dz mz a i e rty τ h,
      denoteTyped_store' I env dz mz _ _ _ rty τ h']
    rcases hs : Term.typeCheck_store_inv h with ⟨k, v, ha, hi, he, hrty, eq⟩
    rcases hs' : Term.typeCheck_store_inv h' with ⟨k', v', ha', hi', he', hrty', eq'⟩
    subst τ
    have hk : k' = k := by
      have hArray := (Term.typeOf_of_typeCheck ha').symm.trans (typeOf_normalizeTerm ha)
      injection hArray with _ hSorts
      injection hSorts with hk
    have hv : v' = v := by
      have hArray := (Term.typeOf_of_typeCheck ha').symm.trans (typeOf_normalizeTerm ha)
      injection hArray with _ hSorts
      injection hSorts with _ hValue
      injection hValue with hv
    subst hk hv
    simp only [cast_eq]
    rw [denote_normalizeTerm I dz mz env a _ ha _ rfl ha',
      denote_normalizeTerm I dz mz env i _ hi _ rfl hi',
      denote_normalizeTerm I dz mz env e _ he _ rfl he']
  | .app (.core .not) [] rty | .app (.core .not) (_ :: _ :: _) rty
  | .app (.core .and) [] rty | .app (.core .and) [_] rty | .app (.core .and) (_ :: _ :: _ :: _) rty
  | .app (.core .or) [] rty | .app (.core .or) [_] rty | .app (.core .or) (_ :: _ :: _ :: _) rty
  | .app (.core .implies) [] rty | .app (.core .implies) [_] rty
  | .app (.core .implies) (_ :: _ :: _ :: _) rty
  | .app (.core .eq) [] rty | .app (.core .eq) [_] rty | .app (.core .eq) (_ :: _ :: _ :: _) rty
  | .app (.core .ite) [] rty | .app (.core .ite) [_] rty | .app (.core .ite) [_, _] rty
  | .app (.core .ite) (_ :: _ :: _ :: _ :: _) rty
  | .app (.core .distinct) [] rty | .app (.core .distinct) [_] rty
  | .app (.num .neg) [] rty | .app (.num .neg) (_ :: _ :: _) rty
  | .app (.num .add) [] rty | .app (.num .add) [_] rty | .app (.num .add) (_ :: _ :: _ :: _) rty
  | .app (.num .sub) [] rty | .app (.num .sub) [_] rty | .app (.num .sub) (_ :: _ :: _ :: _) rty
  | .app (.num .mul) [] rty | .app (.num .mul) [_] rty | .app (.num .mul) (_ :: _ :: _ :: _) rty
  | .app (.num .div) [] rty | .app (.num .div) [_] rty | .app (.num .div) (_ :: _ :: _ :: _) rty
  | .app (.num .mod) [] rty | .app (.num .mod) [_] rty | .app (.num .mod) (_ :: _ :: _ :: _) rty
  | .app (.num .le) [] rty | .app (.num .le) [_] rty | .app (.num .le) (_ :: _ :: _ :: _) rty
  | .app (.num .lt) [] rty | .app (.num .lt) [_] rty | .app (.num .lt) (_ :: _ :: _ :: _) rty
  | .app (.num .ge) [] rty | .app (.num .ge) [_] rty | .app (.num .ge) (_ :: _ :: _ :: _) rty
  | .app (.num .gt) [] rty | .app (.num .gt) [_] rty | .app (.num .gt) (_ :: _ :: _ :: _) rty
  | .app .select [] rty | .app .select [_] rty | .app .select (_ :: _ :: _ :: _) rty
  | .app .store [] rty | .app .store [_] rty | .app .store [_, _] rty
  | .app .store (_ :: _ :: _ :: _ :: _) rty
  | .app (.num .rdiv) _ rty | .app (.num .abs) _ rty
  | .app (.bv _) _ rty | .app (.str _) _ rty
  | .app .option_get _ rty | .app (.datatype_op _ _) _ rty =>
    simp [Term.typeCheck] at h

/-- Normalizing every term of an argument list preserves the values: if `args` type-check as
arguments against the sorts `tys` in a typing context `ctx`, and their normalizations against
`tys` in a typing context `ctx'`, the two lists denote the same values under the same
interpretation of the functions, variable environment and completions of division and modulo by
zero. -/
private theorem denoteArgs_normalizeTerm {σ : SortInterp} {𝒜 : ArrayTheory}
    [SortInterp.AllInhabited σ]
    (I : UFInterp σ 𝒜) (dz mz : Int → Int) {ctx ctx' : TypedContext}
    (env : VarEnv σ 𝒜) (args : List Term) (tys : List TermType)
    (h : Term.typeCheckArgs ctx args tys = true)
    (args' : List Term) (hargs' : args' = args.map normalizeTerm)
    (h' : Term.typeCheckArgs ctx' args' tys = true) :
    Term.denoteTypedArgs I env dz mz args' tys h' =
      Term.denoteTypedArgs I env dz mz args tys h := by
  match args, tys with
  | [], [] => subst hargs'; simp only [List.map_nil, Term.denoteTypedArgs]
  | t :: ts, ty :: tys =>
    subst hargs'
    simp only [List.map_cons, Term.denoteTypedArgs]
    congr 1
    · exact denote_normalizeTerm I dz mz env t ty _ _ rfl _
    · exact denoteArgs_normalizeTerm I dz mz env ts tys _ _ rfl _
  | [], _ :: _ => simp [Term.typeCheckArgs] at h
  | _ :: _, [] => simp [Term.typeCheckArgs] at h
end

/-! ## From terms to queries -/

/-- Entailment by a normalized, possibly smaller query implies entailment by the original. The
original query is a context `ctx` with assumptions `A` and goal `G`. The other is a context `ctx'`
whose every definition is a definition of `ctx` with its body normalized and whose every axiom is
the normalization of an axiom of `ctx`, with the normalized assumptions and goal. Both queries
are assumed well formed: the declared and defined names are distinct and none is a reserved
binder name, each definition body type-checks to its declared sort using only its parameters,
the declared functions and the definitions before it, and every axiom, assumption and goal
type-checks to `Bool`. Nothing else about `ctx'` matters, since the semantics
quantifies over the interpretation of every function. -/
private theorem entails_of_normalize {ctx ctx' : Core.SMT.Context} {A : List Term} {G : Term}
    (hifs : ∀ f ∈ ctx'.ifs.toList,
      ∃ f₀ ∈ ctx.ifs.toList, f = { f₀ with body := normalizeTerm f₀.body })
    (haxms : ∀ a ∈ ctx'.axms.toList, ∃ a₀ ∈ ctx.axms.toList, a = normalizeTerm a₀)
    (hwf : (toSMTQuery ctx A G).WF)
    (hwf' : (toSMTQuery ctx' (A.map normalizeTerm) (normalizeTerm G)).WF) :
    (toSMTQuery ctx' (A.map normalizeTerm) (normalizeTerm G)).EntailsObl hwf' →
    (toSMTQuery ctx A G).EntailsObl hwf := by
  intro hE σ hσ 𝒜 I env dz mz hcons hasserts
  -- Every assertion of the prepared query is the normalization of an assertion that holds.
  have hasserts' : ∀ t (ht : t ∈ (toSMTQuery ctx' (A.map normalizeTerm)
      (normalizeTerm G)).asserts),
      Term.denoteTyped I env dz mz t .bool (hwf'.assertsWF t ht) = true := by
    intro t ht
    have ht₀ : ∃ t₀ ∈ (toSMTQuery ctx A G).asserts, t = normalizeTerm t₀ := by
      simp only [toSMTQuery, SMTQuery.asserts, List.mem_append, List.mem_map] at ht ⊢
      rcases ht with ht | ⟨a, ha, rfl⟩
      · obtain ⟨a₀, ha₀, rfl⟩ := haxms t ht
        exact ⟨a₀, Or.inl ha₀, rfl⟩
      · exact ⟨a, Or.inr ha, rfl⟩
    obtain ⟨t₀, ht₀, rfl⟩ := ht₀
    exact (denote_normalizeTerm I dz mz env t₀ .bool (hwf.assertsWF t₀ ht₀)
      _ rfl (hwf'.assertsWF _ ht)).trans (hasserts t₀ ht₀)
  -- Every definition of the prepared query is the normalization of a definition `I` respects.
  have hcons' : IFs.UFConsistent (toSMTQuery ctx' (A.map normalizeTerm)
      (normalizeTerm G)).fs hwf'.fsTypeCheck I dz mz := by
    intro f hmem hl
    have hmem' : f ∈ ctx'.ifs.toList := by simpa [toSMTQuery, SMTQuery.fs] using hmem
    obtain ⟨f₀, hf₀, rfl⟩ := hifs f hmem'
    have hmem₀ : f₀ ∈ (toSMTQuery ctx A G).fs := by simpa [toSMTQuery, SMTQuery.fs] using hf₀
    have h0 := hcons f₀ hmem₀ hl
    show UF.applyDenoteTyped σ 𝒜 f₀.toUF (I f₀.toUF) hl = _
    rw [h0]
    exact (denote_normalizeTerm I dz mz (hlToEnv f₀.args hl) f₀.body f₀.out
      (hwf.fsTypeCheck f₀ hmem₀) _ rfl (hwf'.fsTypeCheck _ hmem)).symm
  have hG := hE σ hσ 𝒜 I env dz mz hcons' hasserts'
  exact (denote_normalizeTerm I dz mz env G .bool hwf.oblWF _ rfl hwf'.oblWF).symm.trans hG

/-- Entailment by a query carries over to an equal query, whatever the proofs that the two are
well formed. -/
private theorem EntailsObl_congr {q q' : SMTQuery} (h : q = q') (hwf : q.WF) (hwf' : q'.WF) :
    q.EntailsObl hwf → q'.EntailsObl hwf' := by
  subst h; exact id

/-- **Preparation reflects entailment.** If `prepareTerms` accepts a query and the prepared query
entails its goal in every model, then the assembled query (the context that `completeContext`
builds from the query's context, definitions and declarations, with the original assumptions)
entails the original goal in every model. Both queries are assumed to lie in the typed fragment
(`SMTQuery.WF`). -/
theorem prepareTerms_sound
    {context : Core.SMT.Context} {assumptions : List Term} {goal : Term}
    {definitions : List Core.VarDefinition} {declarations : List Core.VarDeclaration}
    {assembled : Core.SMT.Context} {p : PreparedTerms}
    (hassembled : completeContext context definitions declarations = .ok assembled)
    (hprepared : prepareTerms context assumptions goal definitions declarations = .ok p)
    (hwf : (toSMTQuery assembled assumptions goal).WF)
    (hwf' : (toSMTQuery p.context p.assumptions p.goal).WF) :
    (toSMTQuery p.context p.assumptions p.goal).EntailsObl hwf' →
    (toSMTQuery assembled assumptions goal).EntailsObl hwf := by
  obtain ⟨hA, hG, haxms, hifs⟩ := prepareTerms_eq hassembled hprepared
  have hq : toSMTQuery p.context p.assumptions p.goal
      = toSMTQuery p.context (assumptions.map normalizeTerm) (normalizeTerm goal) := by
    rw [hA, hG]
  intro hE
  have hwf'' := hq ▸ hwf'
  exact entails_of_normalize hifs haxms hwf hwf'' (EntailsObl_congr hq hwf' hwf'' hE)

end Strata.SMT.LeanExport
