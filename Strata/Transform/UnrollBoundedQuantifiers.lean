/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.NameMangling
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.Factory
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory

/-! # Unrolling of bounded index quantifiers

Runs after symbolic evaluation. A quantifier whose guard confines its binder to
the indices below a bound of known integer value becomes the conjunction (`∀`) or
disjunction (`∃`) of its instances over that range, each instance substituting
only the index and keeping the guard:

    ∀ i. (0 ≤ i < n) → body    ↦    ⋀_{k<n} (0 ≤ k < n) → body[i ↦ k]

A bound's value is read off the bound itself when it is a literal or evaluates to
one, and otherwise from an equation in scope pinning it. Instances are reduced
afterwards, which discharges the lower bound, resolves nested bounds and drops
branches that cannot hold; the rest of the body stays symbolic. The rewrite
preserves models, and a quantifier whose bound has no known value is left in
place.

The two selectors are related only through the model, so substituting an element
is beyond what the solver could derive from the encoding — and beyond what it can
check. -/

namespace Core.UnrollBoundedQuantifiers

open Lambda Imperative

def selectName : String := seqSelectFunc.name.name
def selectBangName : String := seqSelectUnsafeFunc.name.name
def ltName : String := (intLtFunc (T := CoreLParams)).name.name
def leName : String := (intLeFunc (T := CoreLParams)).name.name
def geName : String := (intGeFunc (T := CoreLParams)).name.name
def gtName : String := (intGtFunc (T := CoreLParams)).name.name
def negName : String := (intNegFunc (T := CoreLParams)).name.name

/-- Demangled base name of an op identifier. Monomorphization mangles
    `Sequence.select!` to `$__mono#Sequence.select!#…`, so op names are compared
    through this. -/
abbrev baseName : String → String := Core.NameMangling.demangledBaseName

/-! ## Caps

Four numbers bound the term the pass emits. The values are arbitrary, and a program
may well state a count above one of them. Hitting a cap leaves that quantifier in
place, but the instances of the enclosing levels have been expanded and reduced by
then, so the work of reaching the cap is already spent. -/

/-- Skip any fold of more than this many instances of one quantifier. -/
def unrollBinderCap : Nat := 64

/-- Skip any fold whose running `∏Nᵢ` would exceed this: nested folds multiply,
    so narrow ranges can still combine into a term too large to emit. -/
def unrollProductCap : Nat := 65536

/-- Nesting depth budget for the fold; a self-referential element fact can cycle
    without changing `∏Nᵢ`. -/
def unrollDepthCap : Nat := 64

/-- Iteration cap for the term normalizer, which otherwise stops once the term
    stops changing. -/
def normIterCap : Nat := 64

/-! ## Value facts (`t == N`)

An equation pinning a term to an integer literal. A quantifier's bound is looked
up here: `length(s) == 3` in scope is what makes `i < length(s)` countable. -/

abbrev IntFactEnv := List (LExpr CoreLParams.mono × Nat)

/-- `(t, N)` if `e` equates the term `t` with the non-negative integer literal `N`. -/
def intFactOf? : LExpr CoreLParams.mono → Option (LExpr CoreLParams.mono × Nat)
  | .eq _ lhs (.const _ (.intConst n)) => if n ≥ 0 then some (lhs, n.toNat) else none
  | .eq _ (.const _ (.intConst n)) rhs => if n ≥ 0 then some (rhs, n.toNat) else none
  | _ => none

mutual
/-- The value facts `s` states unconditionally, so the ones that hold of every
    goal after `s` in its block. -/
def collectAssumeIntFacts (s : Statement) : IntFactEnv :=
  match s with
  | .cmd (.cmd (.assume _ e _)) => (intFactOf? e).elim [] (fun p => [p])
  | .cmd _ => []
  | .block _ ss _ => collectAssumeIntFactsBlock ss
  | .ite _ _ _ _ => []
  | .loop _ _ _ _ _ => []
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
  termination_by structural s

def collectAssumeIntFactsBlock (ss : List Statement) : IntFactEnv :=
  match ss with
  | [] => []
  | s :: rest => collectAssumeIntFacts s ++ collectAssumeIntFactsBlock rest
  termination_by structural ss
end

/-- The value facts that hold everywhere in the program: the ones a top-level
    `Decl.ax` carries. -/
def seedIntFactEnv (prog : Program) : IntFactEnv :=
  prog.decls.foldl (fun acc decl =>
    match decl with
    | .ax a _ => (intFactOf? a.e).elim acc (fun p => p :: acc)
    | _ => acc) []

/-- The value facts the factory's axioms state, such as the `length(empty()) == 0`
    that `Sequence.empty` carries. Monomorphization has already instantiated these
    axioms at their concrete types, so their subjects are the terms a program's own
    occurrences compare equal to. -/
def factoryIntFactEnv (F : @Lambda.Factory CoreLParams) : IntFactEnv :=
  F.toArray.toList.flatMap (fun f => f.axioms.filterMap intFactOf?)

/-- The value an assumption in scope pins for `t`, if one does. Terms are compared
    as written, so a term that only names its value after reduction has to be
    normalized first. -/
def resolveIntFact (env : IntFactEnv) (t : LExpr CoreLParams.mono) : Option Nat :=
  (env.find? (fun (t', _) => t' == t)).map Prod.snd

/-! ## Element facts (`select!(s,k) == elem`)

An equation pinning the element at a literal index of a sequence. Substituting the
element in is what lets an instance of the fold reduce, and what reaches a length
stated of a nested sequence: `length(select!(s,k))` names no value until
`select!(s,k)` is replaced by the element it is pinned to. -/

abbrev SelectEnv := List (LExpr CoreLParams.mono × Nat × LExpr CoreLParams.mono)

/-- `(s, k)` if `e` is `select[!](s, literal k)`. Both names match, so a fact stated
    with one resolves an occurrence of the other: `SeqModel` maps them to the same
    element, `select!` being `select` without its bounds precondition. -/
def selectArgs? : LExpr CoreLParams.mono →
    Option (LExpr CoreLParams.mono × Nat)
  | .app _ (.app _ (.op _ o _) s) (.const _ (.intConst k)) =>
    let bn := baseName o.name
    if (bn == selectName || bn == selectBangName) && k ≥ 0 then some (s, k.toNat)
    else none
  | _ => none

/-- `(s, k, elem)` if `e` states that the element at literal index `k` of `s` is
    `elem`, with either side of the equation carrying the selector. -/
def selectFactOf? : LExpr CoreLParams.mono →
    Option (LExpr CoreLParams.mono × Nat × LExpr CoreLParams.mono)
  | .eq _ lhs rhs =>
    match selectArgs? lhs with
    | some (s, k) => some (s, k, rhs)
    | none => match selectArgs? rhs with
              | some (s, k) => some (s, k, lhs)
              | none => none
  | _ => none

mutual
/-- The element facts `s` states unconditionally. -/
def collectAssumeSelectFacts (s : Statement) : SelectEnv :=
  match s with
  | .cmd (.cmd (.assume _ e _)) => (selectFactOf? e).elim [] (fun p => [p])
  | .cmd _ => []
  | .block _ ss _ => collectAssumeSelectFactsBlock ss
  | .ite _ _ _ _ => []
  | .loop _ _ _ _ _ => []
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
  termination_by structural s

def collectAssumeSelectFactsBlock (ss : List Statement) : SelectEnv :=
  match ss with
  | [] => []
  | s :: rest => collectAssumeSelectFacts s ++ collectAssumeSelectFactsBlock rest
  termination_by structural ss
end

/-- The element facts that hold everywhere in the program: those a `Decl.ax` carries. -/
def seedSelectEnv (prog : Program) : SelectEnv :=
  prog.decls.foldl (fun acc decl =>
    match decl with
    | .ax a _ => (selectFactOf? a.e).elim acc (fun p => p :: acc)
    | _ => acc) []

/-- The element an assumption in scope pins at index `k` of `s`, if one does. -/
def resolveSelect (env : SelectEnv) (s : LExpr CoreLParams.mono) (k : Nat) :
    Option (LExpr CoreLParams.mono) :=
  (env.find? (fun (s', k', _) => k' == k && s' == s)).map (fun (_, _, e) => e)

/-- Replace pinned `select[!](s, literal k)` by its element, top-down. The element
    substituted in is not rescanned, so a fact stating an element in terms of a
    selector on the same sequence cannot substitute without end. -/
def normalizeSelects (env : SelectEnv) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  match selectArgs? e with
  | some (s, k) =>
    match resolveSelect env s k with
    | some elem => elem
    | none =>
      match e with
      | .app m f a => .app m (normalizeSelects env f) (normalizeSelects env a)
      | _ => e
  | none =>
    match e with
    | .app m f a => .app m (normalizeSelects env f) (normalizeSelects env a)
    | .abs m n t b => .abs m n t (normalizeSelects env b)
    | .quant m qk n t tr b => .quant m qk n t tr (normalizeSelects env b)
    | .ite m c t f => .ite m (normalizeSelects env c) (normalizeSelects env t) (normalizeSelects env f)
    | .eq m a b => .eq m (normalizeSelects env a) (normalizeSelects env b)
    | other => other

/-! ## Definitional reduction

`LExpr.eval`, with the program's datatype functions in the factory, does the
selector/tester/`=`/`ite` reduction. It is opaque on quantifiers: it stops at the
first binder it meets, so it is run per instance and handed the largest
quantifier-free subterms rather than the whole term. -/

/-- Fuel for one `eval` call. `evalFully` diverges on a non-value. -/
def evalFuel : Nat := 200

def emptyEnv : Lambda.Env CoreLParams := Lambda.Env.mk (fun _ => none)

/-! The connectives are named by the factory functions the fold is built from, so
the ops this recognizes cannot drift from the ops it emits. -/

def andName : String := (boolAndFunc (T := CoreLParams)).name.name
def orName : String := (boolOrFunc (T := CoreLParams)).name.name
def impliesName : String := (boolImpliesFunc (T := CoreLParams)).name.name

def boolConst? : LExpr CoreLParams.mono → Option Bool
  | .const _ (.boolConst b) => some b
  | _ => none

/-- `(op base name, args)` of an application spine, if the head is an op. -/
def opSpine? : LExpr CoreLParams.mono →
    Option (String × List (LExpr CoreLParams.mono))
  | .op _ o _ => some (baseName o.name, [])
  | .app _ f a => (opSpine? f).map (fun (h, as) => (h, as ++ [a]))
  | _ => none

/-- `and`/`or`/`==>` with one constant argument; `binaryOp` needs both. -/
def foldConnective (e : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  match opSpine? e with
  | some (h, [x, y]) =>
    let bc : Bool → LExpr CoreLParams.mono := fun b => .const () (.boolConst b)
    if h == andName then
      match boolConst? x, boolConst? y with
      | some false, _ | _, some false => bc false
      | some true, _ => y
      | _, some true => x
      | _, _ => e
    else if h == orName then
      match boolConst? x, boolConst? y with
      | some true, _ | _, some true => bc true
      | some false, _ => y
      | _, some false => x
      | _, _ => e
    else if h == impliesName then
      match boolConst? x, boolConst? y with
      | some false, _ | _, some true => bc true
      | some true, _ => y
      | _, _ => e
    else e
  | _ => e

/-- Bottom-up `foldConnective`. -/
def foldConnectives (e : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  foldConnective <|
    match e with
    | .app m f a => .app m (foldConnectives f) (foldConnectives a)
    | .abs m n t b => .abs m n t (foldConnectives b)
    | .quant m k n t tr b => .quant m k n t tr (foldConnectives b)
    | .ite m c t f => .ite m (foldConnectives c) (foldConnectives t) (foldConnectives f)
    | .eq m a b => .eq m (foldConnectives a) (foldConnectives b)
    | other => other

/-- Definitional reduction of `e`. Equivalence-preserving, so running out of fuel
    leaves a partly reduced term equal to `e` rather than a wrong one. -/
def evalTerm (F : @Lambda.Factory CoreLParams) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  foldConnectives (Lambda.LExpr.eval evalFuel F emptyEnv e).fst

/-- The facts a goal may be rewritten with, and the factory reduction runs in. -/
structure UEnv where
  ints : IntFactEnv
  sel : SelectEnv
  F : @Lambda.Factory CoreLParams

/-- The scope a procedure body's traversal starts in: the values the factory's
    axioms fix and what the program states of every execution. The factory's facts
    go first, so a builtin axiom outranks a program axiom naming the same term —
    such a program axiom contradicts the builtins and makes every goal vacuous. -/
def seedUEnv (prog : Program) (F : @Lambda.Factory CoreLParams) : UEnv :=
  ⟨factoryIntFactEnv F ++ seedIntFactEnv prog, seedSelectEnv prog, F⟩

/-- The scope in force after `s`, given the scope before it. What `s` states goes
    first, so between sibling statements the later fact wins the lookup, and within
    one nested block the earlier one does; which of two disagreeing facts wins does
    not matter, since a path stating both makes the obligation vacuous. -/
def extendUEnv (env : UEnv) (s : Statement) : UEnv :=
  { env with ints := collectAssumeIntFacts s ++ env.ints,
             sel := collectAssumeSelectFacts s ++ env.sel }

/-! ## Term normalization -/

/-- Normalize a term for lookup: alternate element substitution with definitional
    reduction to a fixpoint. -/
def normTerm (env : UEnv) (fuel : Nat) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  let e1 := evalTerm env.F (normalizeSelects env.sel e)
  if e1 == e || fuel == 0 then e1 else normTerm env (fuel - 1) e1
  termination_by fuel
  decreasing_by
    rename_i hguard
    simp only [Bool.or_eq_true, Nat.beq_eq_true_eq, not_or] at hguard
    omega

/-! ## Counters

The traversal is pure, so it accumulates counters and the pipeline phase records
them once. They count what the traversal attempted rather than obligations, so one
declined obligation can report a cap per instance of the levels above it. -/

/-- The binder types `ineligible` is reported per. Only `int` is folded today; the
    rest say what a wider fold would have to reach, and `other` can be split — into
    maps or sequences, say — when it is. -/
inductive BinderKind where
  | int | bool | bitvec | other
  deriving DecidableEq

def BinderKind.all : List BinderKind := [.int, .bool, .bitvec, .other]

/-- The kind a binder's type falls under. -/
def BinderKind.ofTy : Option LMonoTy → BinderKind
  | some .int => .int
  | some .bool => .bool
  | some (.bitvec _) => .bitvec
  | _ => .other

instance : ToString BinderKind where
  toString
    | .int => "int"
    | .bool => "bool"
    | .bitvec => "bitvec"
    | .other => "other"

inductive Stats where
  /-- Bounded index quantifiers replaced by a `⋀/⋁_{k<N}` fold of their instances. -/
  | unrolled
  /-- Folds thrown away rather than emitted, either because a fold's instances still
      hold a quantifier or because the whole obligation was restored. -/
  | reverted
  /-- Bounded index quantifiers left in place because a bound's value is
      unknown. -/
  | unresolved
  /-- Quantifiers left in place because their guard states no range the pass
      recognizes, so no count was sought, reported per binder kind. -/
  | ineligible (k : BinderKind)
  /-- Folds declined because one quantifier's count exceeds `unrollBinderCap`, or
      because `∏Nᵢ` would exceed `unrollProductCap`. -/
  | capped
  /-- Folds declined because `unrollDepthCap` fuel ran out. -/
  | depthExhausted
  deriving DecidableEq

instance : ToString Stats where
  toString s :=
    let name := match s with
      | .unrolled => "unrolled"
      | .reverted => "reverted"
      | .unresolved => "unresolved"
      | .ineligible k => s!"ineligible.{k}"
      | .capped => "capped"
      | .depthExhausted => "depthExhausted"
    s!"UnrollBoundedQuantifiers.{name}"

/-- Every counter the pass reports. -/
def Stats.all : List Stats :=
  [.unrolled, .reverted, .unresolved, .capped, .depthExhausted]
    ++ BinderKind.all.map Stats.ineligible

/-- Counters for one run, zero everywhere by default. -/
structure Counts where
  get : Stats → Nat := fun _ => 0

instance : Add Counts where
  add c1 c2 := { get := fun s => c1.get s + c2.get s }

/-- One occurrence of `s`. -/
def Counts.one (s : Stats) : Counts :=
  { get := fun t => if t = s then 1 else 0 }

/-- Move a traversal's folds into `reverted`: its result is being thrown away. The
    counters for quantifiers left in place carry over, since throwing the result
    away restores exactly the quantifiers they describe. -/
def Counts.discardFolds (c : Counts) : Counts :=
  { get := fun s =>
      match s with
      | .unrolled => 0
      | .reverted => c.get .reverted + c.get .unrolled
      | s => c.get s }

/-- Split a traversal's `(result, counts)` pairs into the results and their sum. -/
def unzipCounts {α : Type} (rs : List (α × Counts)) : List α × Counts :=
  (rs.map Prod.fst, rs.foldl (fun acc r => acc + r.snd) {})

/-- The integer value of `t`: the literal it is, else the value a fact in `env`
    states of it, each tried on `t` as written and on its normal form. -/
def resolveIntValue (env : UEnv) (t : LExpr CoreLParams.mono) : Option Int :=
  let valueOf : LExpr CoreLParams.mono → Option Int := fun u =>
    match u with
    | .const _ (.intConst n) => some n
    | _ => (resolveIntFact env.ints u).map Int.ofNat
  match valueOf t with
  | some n => some n
  | none => valueOf (normTerm env normIterCap t)

/-! ## Eligibility: which quantifiers range over `[0, n)`

Replacing `∀ i. body` by `⋀_{k<n} body[i ↦ k]` keeps the same models only when
every index outside `[0, n)` already makes the body true, and dually false for
`∃`. A guard conjunct `0 ≤ i` beside a conjunct `i < ub` establishes that. -/

/-- Operands of `e` when it applies a binary op whose demangled name is `name`. -/
def binOpArgs? (name : String) : LExpr CoreLParams.mono →
    Option (LExpr CoreLParams.mono × LExpr CoreLParams.mono)
  | .app _ (.app _ (.op _ o _) x) y =>
    if baseName o.name == name then some (x, y) else none
  | _ => none

/-- Top-level conjuncts of `e`, splitting `Bool.And` and nothing else. A
    disjunction, a negation or a binder comes back whole, since a comparison inside
    one need not hold of every index. -/
def conjuncts : LExpr CoreLParams.mono → List (LExpr CoreLParams.mono)
  | e@(.app _ (.app _ (.op _ o _) x) y) =>
    if baseName o.name == andName then conjuncts x ++ conjuncts y else [e]
  | e => [e]

/-- Conjuncts of the antecedents along `e`'s implication chain, empty if `e` is
    not an implication. `G₁ → G₂ → R` restricts an index exactly as
    `G₁ ∧ G₂ → R` does. -/
def antecedentConjuncts : LExpr CoreLParams.mono → List (LExpr CoreLParams.mono)
  | .app _ (.app _ (.op _ o _) g) r =>
    if baseName o.name == impliesName then conjuncts g ++ antecedentConjuncts r
    else []
  | _ => []

/-- Conjuncts of a quantifier body that can restrict its binder's range: for `∀`
    the antecedents of the body's implication chain, for `∃` the body's own
    conjuncts. Nothing here descends through `.quant` or `.abs`, so `.bvar 0` in a
    conjunct returned is the quantifier's own binder. -/
def guardConjuncts (qk : QuantifierKind) (body : LExpr CoreLParams.mono) :
    List (LExpr CoreLParams.mono) :=
  match qk with
  | .all => antecedentConjuncts body
  | .exist => conjuncts body

/-- The term bounding the binder above, if `e` is such a bound, and whether the
    bound is strict: `binder < ub` is, `binder ≤ ub` is not. -/
def upperBound? (e : LExpr CoreLParams.mono) :
    Option (LExpr CoreLParams.mono × Bool) :=
  match binOpArgs? ltName e with
  | some (.bvar _ 0, ub) => some (ub, true)
  | _ =>
    match binOpArgs? leName e with
    | some (.bvar _ 0, ub) => some (ub, false)
    | _ => none

/-- The integer `e` denotes, if it is a literal. A negative one is written
    `Int.Neg` of a literal, there being no negative literal in the surface syntax. -/
def intLiteral? : LExpr CoreLParams.mono → Option Int
  | .const _ (.intConst c) => some c
  | .app _ (.op _ o _) (.const _ (.intConst c)) =>
    if baseName o.name == negName then some (-c) else none
  | _ => none

/-- Does `e` bound the binder below by a literal, admitting no negative index? The
    binder must be the subject: `0 ≤ length(s)` constrains no index, yet has the same
    shape. A strict bound admits from `c + 1`, so `-1` is the least literal it takes. -/
def isLowerBounded (e : LExpr CoreLParams.mono) : Bool :=
  match binOpArgs? leName e, binOpArgs? geName e,
        binOpArgs? ltName e, binOpArgs? gtName e with
  | some (lo, .bvar _ 0), _, _, _ => (intLiteral? lo).any (fun c => decide (0 ≤ c))
  | _, some (.bvar _ 0, lo), _, _ => (intLiteral? lo).any (fun c => decide (0 ≤ c))
  | _, _, some (lo, .bvar _ 0), _ => (intLiteral? lo).any (fun c => decide (-1 ≤ c))
  | _, _, _, some (.bvar _ 0, lo) => (intLiteral? lo).any (fun c => decide (-1 ≤ c))
  | _, _, _, _ => false

/-- The upper bounds a quantifier's guard places on its binder, in the order the
    guard states them, for a guard that also bounds the binder below by a
    non-negative literal; empty otherwise. -/
def rangeUBs (qk : QuantifierKind) (body : LExpr CoreLParams.mono) :
    List (LExpr CoreLParams.mono × Bool) :=
  let gs := guardConjuncts qk body
  if gs.any isLowerBounded then gs.filterMap upperBound? else []

/-- Does the pass attempt a fold on a quantifier of this kind and body? -/
def attemptsFold (qk : QuantifierKind) (body : LExpr CoreLParams.mono) : Bool :=
  !(rangeUBs qk body).isEmpty

/-- How many indices, counting from zero, a bound of this strictness admits:
    `[0, ub)` for a strict bound and `[0, ub]` for a non-strict one. -/
def indexCount (ub : Int) (strict : Bool) : Nat :=
  let hi := if strict then ub else ub + 1
  if hi ≤ 0 then 0 else hi.toNat

/-- The number of instances a quantifier bounded above by `ub` has, when `ub`'s
    value is known. The count can exceed the binder's true range, since a guard
    stating several upper bounds is read from whichever one resolves rather than
    from the least; that only costs term size, because every instance keeps the
    guard and so an instance outside the range holds vacuously. An undercount would
    instead drop instances and weaken the goal, so a count is only ever read off a
    bound whose value a fact states outright. -/
def resolveCount (env : UEnv) (ub : LExpr CoreLParams.mono) (strict : Bool) :
    Option Nat :=
  (resolveIntValue env ub).map (indexCount · strict)

/-- Whether `e` holds a quantifier anywhere, of any kind. -/
def containsQuant : LExpr CoreLParams.mono → Bool
  | .quant _ _ _ _ _ _ => true
  | .app _ f a => containsQuant f || containsQuant a
  | .abs _ _ _ b => containsQuant b
  | .ite _ c t f => containsQuant c || containsQuant t || containsQuant f
  | .eq _ a b => containsQuant a || containsQuant b
  | _ => false

/-- Does `e` reference any of the `depth` binders enclosing it? -/
def refsEnclosing (depth : Nat) (e : LExpr CoreLParams.mono) : Bool :=
  (List.range depth).any (fun i => LExpr.bvarUsed i e)

/-- Reduce the maximal subterms `eval` can act on: quantifier-free, and closed with
    respect to the enclosing binders, since `eval` contracts a redex with `subst`,
    which does not lift bound variables and would capture such a subterm. -/
def reduceUnderBinders (env : UEnv) (depth : Nat) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  if !containsQuant e && !refsEnclosing depth e then evalTerm env.F e
  else
    match e with
    | .quant m k n t tr b => .quant m k n t tr (reduceUnderBinders env (depth + 1) b)
    | .abs m n t b => .abs m n t (reduceUnderBinders env (depth + 1) b)
    | .app m f a => .app m (reduceUnderBinders env depth f) (reduceUnderBinders env depth a)
    | .ite m c t f =>
      .ite m (reduceUnderBinders env depth c) (reduceUnderBinders env depth t)
        (reduceUnderBinders env depth f)
    | .eq m a b => .eq m (reduceUnderBinders env depth a) (reduceUnderBinders env depth b)
    | other => other

/-- Resolve the elements a literal index pins, then reduce. -/
def reduceInstance (env : UEnv) (depth : Nat) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  foldConnectives (reduceUnderBinders env depth (normalizeSelects env.sel e))

/-- Conjoin (`.all`) or disjoin (`.exist`) the instances. No instances leaves the
    connective's unit, which is the quantifier's value over an empty range. -/
def combineFold (qk : QuantifierKind) (ts : List (LExpr CoreLParams.mono)) :
    LExpr CoreLParams.mono :=
  match qk with
  | .all => ts.foldr (fun t acc =>
      .app () (.app () (boolAndFunc (T := CoreLParams)).opExpr t) acc)
      (.const () (.boolConst true))
  | .exist => ts.foldr (fun t acc =>
      .app () (.app () (boolOrFunc (T := CoreLParams)).opExpr t) acc)
      (.const () (.boolConst false))

/-- Replace each bounded index quantifier whose count resolves by `⋀/⋁_{k<n}` of
    the index-substituted body, recursing into the instances for nested
    quantifiers, and return the rewritten term with the counters accumulated. A
    quantifier stays in place where its count does not resolve or where a cap or
    `fuel` stops the fold. `depth` is the number of binders `e` sits under, which
    the per-instance reduction needs to recognize a bound variable of an enclosing
    quantifier.

    A quantifier that stays in place has its trigger rewritten along with its body,
    and one that is unrolled takes its trigger with it; a trigger is a pattern for
    instantiation, not part of what the formula says. -/
def unrollExpr (env : UEnv) (fuel : Nat) (prod : Nat) (depth : Nat)
    (e : LExpr CoreLParams.mono) : LExpr CoreLParams.mono × Counts :=
  match e with
  | .quant m qk n t tr body =>
    let keep : Unit → LExpr CoreLParams.mono × Counts := fun _ =>
      let (tr', ctr) := unrollExpr env fuel prod (depth + 1) tr
      let (body', cbody) := unrollExpr env fuel prod (depth + 1) body
      (.quant m qk n t tr' body', ctr + cbody)
    let ubs := rangeUBs qk body
    if ubs.isEmpty then
      let (kept, ckept) := keep ()
      (kept, ckept + Counts.one (.ineligible (BinderKind.ofTy t)))
    else
      match ubs.findSome? (fun (ub, strict) => resolveCount env ub strict) with
      | some cnt =>
        if cnt > unrollBinderCap || prod * cnt > unrollProductCap then
          (e, Counts.one .capped)
        else
          match fuel with
          | 0 => (e, Counts.one .depthExhausted)
          | fuel' + 1 =>
            -- `betaReduce` discharges this binder and lowers the enclosing ones,
            -- so an instance sits under the same `depth` binders as the quantifier.
            let (instances, cinst) := unzipCounts ((List.range cnt).map (fun k =>
              unrollExpr env fuel' (prod * cnt) depth
                (reduceInstance env depth
                  (LExpr.betaReduce (.const () (.intConst (Int.ofNat k))) body))))
            let folded := foldConnectives (combineFold qk instances)
            -- Stricter than the per-obligation rule: an instance copies what is inside it.
            if containsQuant folded then (e, cinst.discardFolds + Counts.one .reverted)
            else (folded, cinst + Counts.one .unrolled)
      | none =>
        let (kept, ckept) := keep ()
        (kept, ckept + Counts.one .unresolved)
  | .app m f a =>
    let (f', cf) := unrollExpr env fuel prod depth f
    let (a', ca) := unrollExpr env fuel prod depth a
    (.app m f' a', cf + ca)
  | .abs m n t b =>
    let (b', cb) := unrollExpr env fuel prod (depth + 1) b
    (.abs m n t b', cb)
  | .ite m c t f =>
    let (c', cc) := unrollExpr env fuel prod depth c
    let (t', ct) := unrollExpr env fuel prod depth t
    let (f', cf) := unrollExpr env fuel prod depth f
    (.ite m c' t' f', cc + ct + cf)
  | .eq m a b =>
    let (a', ca) := unrollExpr env fuel prod depth a
    let (b', cb) := unrollExpr env fuel prod depth b
    (.eq m a' b', ca + cb)
  | other => (other, {})
  -- The structural branches keep `fuel`, so the lexicographic pair is needed.
  termination_by (fuel, e)

/-- Is any quantifier the pass attempts a fold on still standing? This also covers
    the ones a cap declined, whose counts do resolve. -/
def hasBoundedQuant : LExpr CoreLParams.mono → Bool
  | .quant _ qk _ _ tr body =>
    attemptsFold qk body || hasBoundedQuant tr || hasBoundedQuant body
  | .app _ f a => hasBoundedQuant f || hasBoundedQuant a
  | .abs _ _ _ b => hasBoundedQuant b
  | .ite _ c t f => hasBoundedQuant c || hasBoundedQuant t || hasBoundedQuant f
  | .eq _ a b => hasBoundedQuant a || hasBoundedQuant b
  | _ => false

/-- All or nothing per obligation: the goal returned is either fully unrolled or the
    one that arrived. A quantifier the pass never attempted is no obstacle. Part fold
    and part quantifier can be harder to refute than either whole form, at the price
    of the folds of a resolvable quantifier beside an unresolvable one. -/
def processExpr (env : UEnv) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono × Counts :=
  let (e', counts) := unrollExpr env unrollDepthCap 1 0 e
  if hasBoundedQuant e' then (e, counts.discardFolds) else (e', counts)

/-- Goals only: `assert` and `cover` are rewritten, and every other command is
    returned as it stands. Unrolling an `assume` would state it only of the range a
    resolved count covers rather than of every index. -/
def unrollCmd (env : UEnv) : Command → Command × Counts
  | .cmd (.assert l e md) =>
    let (e', c) := processExpr env e
    (.cmd (.assert l e' md), c)
  | .cmd (.cover l e md) =>
    let (e', c) := processExpr env e
    (.cmd (.cover l e' md), c)
  | c => (c, {})

/-! ## Program traversal

Symbolic evaluation packs each obligation into its own `.ite .nondet` branch beside
the assumptions it was generated under, so reaching the goals means descending into
those branches. An `.ite` contributes no facts of its own and both arms are
traversed in the scope in force before it, which keeps a fact assumed inside one
branch off the goals of every other. -/

mutual
def unrollStmt (env : UEnv) (s : Statement) : Statement × Counts :=
  match s with
  | .cmd c =>
    let (c', cc) := unrollCmd env c
    (.cmd c', cc)
  | .block l ss md =>
    let (ss', css) := unrollBlock env ss
    (.block l ss' md, css)
  | .ite c tss ess md =>
    let (tss', ctss) := unrollBlock env tss
    let (ess', cess) := unrollBlock env ess
    (.ite c tss' ess' md, ctss + cess)
  -- Left alone, along with CFG bodies below: the phase requires `noLoops` and
  -- `noCFGBodies`, so neither shape reaches this traversal.
  | .loop g measure inv body md => (.loop g measure inv body md, {})
  | .exit l md => (.exit l md, {})
  | .funcDecl decl md => (.funcDecl decl md, {})
  | .typeDecl tc md => (.typeDecl tc md, {})
  termination_by Imperative.Stmt.sizeOf s

def unrollBlock (env : UEnv) (ss : List Statement) : List Statement × Counts :=
  match ss with
  | [] => ([], {})
  | s :: rest =>
    let (s', cs) := unrollStmt env s
    let (rest', crest) := unrollBlock (extendUEnv env s) rest
    (s' :: rest', cs + crest)
  termination_by Imperative.Block.sizeOf ss
end

/-- Unroll the bounded index quantifiers in every procedure's goals, each in the
    scope of the assumptions reaching it, summing the counters over the program. -/
def unrollBoundedQuantifiersProgram (F : @Lambda.Factory CoreLParams) (p : Program) :
    Program × Counts :=
  let env := seedUEnv p F
  let (decls, counts) := unzipCounts (p.decls.map fun decl =>
      match decl with
      | .proc proc md =>
        let (body, cbody) := match proc.body with
          | .structured ss =>
            let (ss', css) := unrollBlock env ss
            (.structured ss', css)
          | .cfg g => (.cfg g, {})
        (.proc { proc with body := body } md, cbody)
      | d => (d, {}))
  ({ decls := decls }, counts)

end Core.UnrollBoundedQuantifiers

public section

/-- Unroll every bounded index quantifier whose count resolves into `⋀/⋁_{k<n}` by
    pure index substitution. Runs after symbolic evaluation; model-preserving.

    The pass runs in a local copy of the factory with the program's datatype
    functions added, which the per-instance reduction needs to reduce a selector or
    a tester; the transform state's factory is left as it was.

    `staticSingleAssignment` is what keeps a count true where it is used: were its
    subject reassigned between the `assume` stating it and the goal, the fold would
    range over the old value and drop conjuncts. -/
def Core.unrollBoundedQuantifiersPipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "unrollBoundedQuantifiers"
    (requires := factSet![.noCFGBodies, .noLoops, .staticSingleAssignment])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noPrecondsFromFuncs,
                         .noNondetGuards, .noInternalFuncDecl, .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated])
    fun prog => do
      let baseF ← Core.Transform.getFactory
      let blocks := prog.decls.filterMap fun d =>
        match d with | .type (.data b) _ => some b | _ => none
      -- Neither can fail on a program that reaches this phase: type checking makes
      -- the same two calls and rejects a block whose generated names collide.
      let F := blocks.foldl (fun F b =>
        match Lambda.genBlockFactory (T := Core.CoreLParams) b with
        | .ok bf => (F.addFactory bf).toOption.getD F
        | .error _ => F) baseF
      let (prog', counts) := Core.UnrollBoundedQuantifiers.unrollBoundedQuantifiersProgram F prog
      for s in Core.UnrollBoundedQuantifiers.Stats.all do
        Core.Transform.incrementStat s!"{s}" (counts.get s)
      -- Over-approximates on an obligation whose folds were all reverted, since the
      -- goal is then returned as it arrived while `reverted` counts the attempts.
      return (counts.get .unrolled > 0 || counts.get .reverted > 0, prog')

end -- public section
