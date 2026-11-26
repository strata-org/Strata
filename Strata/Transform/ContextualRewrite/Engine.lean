/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.EqualitySimplification.Facts
public import Strata.Languages.Core.Factory

/-! # Contextual rewriting: the engine

A rewriter for Core terms under the facts that hold at a point of a program. It is
parameterized by a collection of conditional rewrite rules (`CondRule`, gathered in an `Env`);
the rules themselves are in `ContextualRewrite.Rules`.

Code that walks a program, such as the `contextualRewrite` phase (`Core.contextualRewritePhase`),
keeps a `Facts` value for each program point, the facts that hold in every state reaching it,
and updates it with:

* `Facts.empty`: no facts, at the start of a procedure;
* `Facts.unreachable`: at a point no state reaches, such as after an `exit`;
* `Facts.assume env fs e`: after `assume e`;
* `Facts.forget fs xs`: after a write to the variables `xs`;
* `Facts.join f g`: where a path on which `f` holds meets one on which `g` holds.

`rewrite env fs e` gives a term with the value of `e` in every state where `fs` holds, and
`closes env fs e` says whether that term is `true`.

## Learning an assumption

`Facts.assume env fs e` rewrites `e` under `fs` and records what the result says. If the
result is `false`, no state satisfies the path's assumptions and the path is marked dead.
Otherwise:

* if `e` is an equation `x == d`, where `x` has no definition and `d` does not mention `x` and
  is not a value or a constructor application, the definition `x := d` is recorded;
* the result is split into literals, each a term with its value (`literals`): the literals of
  each operand of a conjunction, `t ↦ false` for `¬t`, `x ↦ v` for an equation between `x`
  and a value or constructor application `v`, and `t ↦ true` for any other Boolean term;
* a literal that gives a Boolean variable with a definition a value also gives the literals
  of the definition;
* a literal `a ⇒ d ↦ true` records the conditional fact "where `a` is `true`, `d` holds", and
  `a ∨ d ↦ true` records "where `a` is `false`, `d` holds" and the same with `a` and `d`
  swapped (`CondFact`);
* a literal that matches the condition of a conditional fact makes its conclusion an
  assumption, learned in turn.

## Rewriting a term

`rewrite` walks a term bottom up. At each node it:

1. rewrites the children, under the context: the facts of the path, and the inner facts
   (`InnerFact`) of the conditions passed on the way down. The context changes only here:
   * `ite c a b`: `c` is rewritten first. If it becomes a literal, the node becomes the branch
     it selects. Otherwise `a` is rewritten with the literals of `c` assumed true, `b` with
     them assumed false;
   * `a ∧ b` and `a ⇒ b`: `b` is rewritten with `a` assumed true;
   * `a ∨ b`: `b` is rewritten with `a` assumed false;
   * under a binder, inner facts that mention a bound variable are dropped;
2. looks the node up in the context. An inner fact or a fact of the path that gives the node a
   value replaces it;
3. tries the rules for the node's operator, in order (`CondRule`). A rule that applies gives a
   right-hand side and hypotheses. It fires when each hypothesis rewrites to `true` one
   backchaining level deeper (`maxBackchain`), or, at the last level, when the facts give the
   hypothesis `true` directly. The first rule that fires replaces the node by its right-hand
   side, rewritten; parts of the node that it reuses are already rewritten and are kept as
   they are;
4. when no rule fired: if an argument whose head a rule reads (`CondRule.needsHead`) is a
   variable with a definition, the node is rewritten again with the definition in its place.
   For a Boolean node the result is kept only when it is a literal, so that facts about the
   node as written still match it.

## Budgets

A budget that runs out leaves the rest of a term as it is.

* `maxTreeSize`: the largest tree of a goal or an assumption the engine works on;
* `maxSteps`: how many steps one goal or assumption may take;
* `Definition.expandedSize`: what reading through a definition costs, out of an allowance of
  `maxTreeSize` nodes per goal or assumption;
* `maxBackchain`: how deep backchaining goes;
* `defDepth`: how many definitions are read through in a row.

## Soundness

The rewrite of a term has the term's value in every state where the facts hold. It may
mention fewer variables than the term, since a subterm can be replaced by the value the facts
give it, and may mention variables of the facts, such as those of a definition it reads
through.

This assumes one thing of the model: the operators each theory recognizes mean what the
theory says. For the environment of a function table, this follows from the model being
consistent with the table and its testers meaning what they say.

The facts are sound too: the empty facts hold in every state; the facts after `assume e` hold
where the facts before it and `e` do; the facts without those that mention `xs` hold in every
state that agrees, outside `xs`, with one where the facts hold; the join holds where either
side holds; and facts marked dead hold in no state.
-/

namespace Core.ContextualRewrite

open Lambda hiding Env

public section

/-! ## Budgets -/

/-- The largest tree, in nodes (`LExpr.size`), of a goal or an assumption the engine works on.
    A goal with a larger tree is left as it is, and an assumption with a larger tree gives no
    fact. A term that shares subterms can have a tree much larger than its representation in
    memory, and rewriting walks the tree. -/
def maxTreeSize : Nat := 100000

/-- How many steps one goal or one assumption may take: a step is a visit of a node or an
    attempt of a rule. -/
def maxSteps : Nat := 10 * maxTreeSize

/-- How many rules may be applied in a row to discharge hypotheses: a hypothesis of a rule
    applied while discharging another rule's hypothesis is one level deeper. -/
def maxBackchain : Nat := 3

/-- How many definitions may be read through in a row. It also bounds how many conditional
    facts an assumption follows in a row. -/
def defDepth : Nat := 16

/-! ## Terms with their hash -/

/-- A term with its hash `LExpr.hashExpr`, which facts are looked up by. -/
structure HExpr where
  e : Expression.Expr
  h : EqualitySimplification.HashOf e

namespace HExpr

/-- `e` with its hash. -/
@[inline] def of (e : Expression.Expr) : HExpr := ⟨e, LExpr.hashExpr e, rfl⟩

/-- `f a`. -/
@[inline] def app (m : ExprSourceLoc) (f a : HExpr) : HExpr :=
  ⟨.app m f.e a.e, LExpr.hashApp f.h.1 a.h.1, by simp only [LExpr.hashExpr, f.h.2, a.h.2]⟩

/-- `a == b`. -/
@[inline] def eq (m : ExprSourceLoc) (a b : HExpr) : HExpr :=
  ⟨.eq m a.e b.e, LExpr.hashEqExpr a.h.1 b.h.1, by simp only [LExpr.hashExpr, a.h.2, b.h.2]⟩

/-- `ite c t f`. -/
@[inline] def ite (m : ExprSourceLoc) (c t f : HExpr) : HExpr :=
  ⟨.ite m c.e t.e f.e, LExpr.hashIte c.h.1 t.h.1 f.h.1,
    by simp only [LExpr.hashExpr, c.h.2, t.h.2, f.h.2]⟩

/-- The abstraction with body `b`. -/
@[inline] def abs (m : ExprSourceLoc) (name : String) (ty : Option LMonoTy) (b : HExpr) :
    HExpr :=
  ⟨.abs m name ty b.e, LExpr.hashAbs (hash name) (LExpr.hashOptTy ty) b.h.1,
    by simp only [LExpr.hashExpr, b.h.2]⟩

/-- The quantifier `.quant m k name ty tr b`. -/
@[inline] def quant (m : ExprSourceLoc) (k : QuantifierKind) (name : String)
    (ty : Option LMonoTy) (tr : Expression.Expr) (b : HExpr) : HExpr :=
  let kh : UInt64 := match k with | .all => 0 | .exist => 1
  ⟨.quant m k name ty tr b.e,
    LExpr.hashQuantExpr kh (hash name) (LExpr.hashOptTy ty) (LExpr.hashExpr tr) b.h.1,
    by simp only [LExpr.hashExpr, b.h.2]; rfl⟩

/-- The application of `head` to `args`, each argument applied at its location. -/
def applyAll (head : HExpr) (args : List (ExprSourceLoc × HExpr)) : HExpr :=
  args.foldl (fun acc (m, a) => HExpr.app m acc a) head

end HExpr

/-! ## Terms -/

/-- Literal `true` or `false`. -/
@[inline] def boolLit (b : Bool) : Expression.Expr := .boolConst valueLoc b

/-- Whether `e` is a literal constant. -/
@[inline] def isConst : Expression.Expr → Bool
  | .const .. => true
  | _ => false

/-- `e` as an operator applied to arguments, with the arguments `acc` already collected
    appended. Each argument comes with the location of the application node that applies it.
    For example, `spine? (.app m₂ (.app m₁ f a) b) [] = some (f, [(m₁, a), (m₂, b)])` for an
    operator `f`, and a term whose head is not an operator gives `none`. -/
def spine? : Expression.Expr → List (ExprSourceLoc × Expression.Expr) →
    Option (Expression.Expr × List (ExprSourceLoc × Expression.Expr))
  | .app m f a, acc => spine? f ((m, a) :: acc)
  | e@(.op ..), acc => some (e, acc)
  | _, _ => none

/-- The application of `head` to `args`. -/
def applyArgs (head : Expression.Expr) (args : List (ExprSourceLoc × Expression.Expr)) :
    Expression.Expr :=
  args.foldl (fun acc (m, a) => .app m acc a) head

/-- The operands of `e`: the arguments of an operator application, the sides of an equation,
    the parts of an `ite`, the body of a binder. -/
def operands (e : Expression.Expr) : List Expression.Expr :=
  match e with
  | .eq _ a b => [a, b]
  | .ite _ c a b => [c, a, b]
  | .abs _ _ _ b | .quant _ _ _ _ _ b => [b]
  | .app .. => match spine? e [] with
    | some (_, args) => args.map (·.2)
    | none => []
  | _ => []

/-- The operands of `e` and their operands: the parts a rule builds its right-hand side and
    hypotheses from. They are already rewritten. -/
def pieces (e : Expression.Expr) : List Expression.Expr :=
  let ps := operands e
  ps ++ ps.flatMap operands

/-- `e` with its operand `i` (as `operands` counts them) replaced by `d`, for an operator
    application or an equation. -/
def setOperand (e : Expression.Expr) (i : Nat) (d : Expression.Expr) : Expression.Expr :=
  match e with
  | .eq m a b => if i == 0 then .eq m d b else if i == 1 then .eq m a d else e
  | .app .. => match spine? e [] with
    | some (head, args) =>
      match args[i]? with
      | some (m, _) => applyArgs head (args.set i (m, d))
      | none => e
    | none => e
  | _ => e

/-- The type `ty` gives a value after `n` arguments. -/
def resultTy : LMonoTy → Nat → Option LMonoTy
  | ty, 0 => some ty
  | .tcons "arrow" [_, r], n + 1 => resultTy r n
  | _, _ => none

/-- Whether `e` is Boolean by its shape: an equation, a quantifier, or an application of an
    operator annotated with a type whose result is `bool`. -/
def isBoolNode (e : Expression.Expr) : Bool :=
  match e with
  | .eq .. | .quant .. => true
  | .app .. => match spine? e [] with
    | some (.op _ _ (some ty), args) => resultTy ty args.length == some .bool
    | _ => false
  | _ => false

/-- Whether `e` is a variable annotated `bool`. -/
def isBoolVar : Expression.Expr → Bool
  | .fvar _ _ (some ty) => ty == LMonoTy.bool
  | _ => false

/-! ## Connectives -/

/-- A binary Boolean connective: `∧`, `∨` or `⇒`. -/
inductive BinConn where
  | and | or | implies

/-- A Boolean connective applied to its operands: `¬ a`, or `a ∧ b`, `a ∨ b`, `a ⇒ b`. -/
inductive Conn where
  | not (a : Expression.Expr)
  | bin (k : BinConn) (a b : Expression.Expr)

/-- The operands of a connective. -/
def Conn.operands : Conn → List Expression.Expr
  | .not a => [a]
  | .bin _ a b => [a, b]

/-- `e` as `¬`, `∧`, `∨` or `⇒` applied to its operands, where `cs` gives the connective each
    function denotes, by name. For example, `Conn.of? cs (Bool.And p q) = some (.bin .and p q)`.
    The engine and the theories recognize connectives with this function. -/
def Conn.of? (cs : Std.HashMap String BoolOpKind) : Expression.Expr → Option Conn
  | .app _ (.op _ o _) a => if cs.get? o.name == some .Not then some (.not a) else none
  | .app _ (.app _ (.op _ o _) a) b =>
    match cs.get? o.name with
    | some .And => some (.bin .and a b)
    | some .Or => some (.bin .or a b)
    | some .Implies => some (.bin .implies a b)
    | _ => none
  | _ => none

/-- The operands of a connective are smaller than it. -/
theorem Conn.of?_lt {cs : Std.HashMap String BoolOpKind} {e : Expression.Expr} {c : Conn}
    (h : Conn.of? cs e = some c) : ∀ a ∈ c.operands, sizeOf a < sizeOf e := by
  unfold Conn.of? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp [Conn.operands] <;> omega

/-! ## Rules -/

/-- What a rule is about: an operator (alone or applied to arguments), an equation, an `ite`,
    or a quantifier. -/
inductive Head where
  | op (name : String)
  | eq
  | ite
  | quant
  deriving Inhabited

/-- What `e` is about, as a rule sees it. -/
def headOf : Expression.Expr → Option Head
  | .op _ o _ => some (.op o.name)
  | .eq .. => some .eq
  | .ite .. => some .ite
  | .quant .. => some .quant
  | e@(.app ..) => match spine? e [] with
    | some (.op _ o _, _) => some (.op o.name)
    | _ => none
  | _ => none

/-- A conditional rewrite rule, over what a theory knows about a program (`σ`): on a term, at
    most one candidate right-hand side and the hypotheses under which the term and the
    right-hand side have the same value. A rule does not read the facts; what it needs of the
    context it states as hypotheses.

    What a rule must satisfy: in every model in which the theory's operators have their
    meaning, if every hypothesis has the value `true`, the term and the right-hand side have
    the same value; the right-hand side and the hypotheses add no free variable, keep the
    operators consistent with the program's function table, the right-hand side has every
    type the term has, and each hypothesis is Boolean. -/
structure CondRule (σ : Type) where
  /-- A name for the rule. -/
  name : String
  /-- Whether the rule may apply to a term with the head `h`. The engine tries a rule only on
      such terms; the rule's `apply` decides. -/
  heads : σ → Head → Bool
  /-- The operand positions (as `operands` counts them) whose head the rule reads on the
      term. When the rule does not apply and such an operand is a variable with a definition,
      the engine retries with the definition there. -/
  needsHead : σ → Expression.Expr → List Nat := fun _ _ => []
  /-- The deepest backchaining level the hypotheses are rewritten at, if lower than the
      engine's. `some 0`: each hypothesis must hold by the facts directly. -/
  hypDepth : Option Nat := none
  /-- The right-hand side and the hypotheses, or `none` when the rule does not apply. -/
  apply : σ → Expression.Expr → Option (Expression.Expr × List Expression.Expr)

/-- `r` over `σ`, reading what it needs through `f`. -/
def CondRule.lift {σ τ : Type} (f : σ → τ) (r : CondRule τ) : CondRule σ where
  name := r.name
  heads s := r.heads (f s)
  needsHead s := r.needsHead (f s)
  hypDepth := r.hypDepth
  apply s := r.apply (f s)

/-! ## The environment -/

variable {σ : Type}

/-- What the engine knows about a program: its function table, the connectives in it, what
    the theories know (`theories`), and the theories' rules, indexed by what they are about,
    each list in the order its rules are tried. -/
structure Env (σ : Type) where
  /-- The program's function table. -/
  functions : Lambda.Factory CoreLParams
  /-- The functions of `functions` that are Boolean connectives, by name. -/
  connectives : Std.HashMap String BoolOpKind := {}
  /-- What the theories know about the program. -/
  theories : σ
  /-- The rules for each operator of `functions`. -/
  byOp : Std.HashMap String (List (CondRule σ)) := {}
  /-- The rules for equations. -/
  eqRules : List (CondRule σ) := []
  /-- The rules for `ite`s. -/
  iteRules : List (CondRule σ) := []
  /-- The rules for quantifiers. -/
  quantRules : List (CondRule σ) := []
  /-- Whether the function table has the operators the rules build. When it does not, the
      engine learns nothing and rewrites nothing. -/
  enabled : Bool := true

/-- The environment for `functions`, `connectives`, `theories` and `rules`, with the rules
    indexed by what they are about. -/
def Env.build (functions : Lambda.Factory CoreLParams)
    (connectives : Std.HashMap String BoolOpKind) (theories : σ) (rules : List (CondRule σ))
    (enabled : Bool) : Env σ :=
  let byOp := functions.toArray.foldl (init := ({} : Std.HashMap String (List (CondRule σ))))
    fun m f =>
      let rs := rules.filter (·.heads theories (.op f.name.name))
      if rs.isEmpty then m else m.insert f.name.name rs
  { functions, connectives, theories, byOp, enabled,
    eqRules := rules.filter (·.heads theories .eq)
    iteRules := rules.filter (·.heads theories .ite)
    quantRules := rules.filter (·.heads theories .quant) }

/-- The rules for the term `e`. An operator that is not a function of the table has none. -/
def Env.rulesFor (env : Env σ) (e : Expression.Expr) : List (CondRule σ) :=
  match headOf e with
  | some (.op n) => env.byOp.getD n []
  | some .eq => env.eqRules
  | some .ite => env.iteRules
  | some .quant => env.quantRules
  | none => []

/-- `e` as a connective of `env` applied to its operands. -/
@[inline] def Env.conn? (env : Env σ) (e : Expression.Expr) : Option Conn :=
  Conn.of? env.connectives e

/-! ## Facts -/

/-- A variable's definition on the path. -/
structure Definition where
  /-- The definition as the assumption states it. -/
  written : Expression.Expr
  /-- `written` rewritten under the facts when it was learned: also the variable's value
      wherever the facts hold. Reading through the definition reads this. -/
  simplified : Expression.Expr
  /-- The number of nodes of the tree of `written` with each variable that has a definition
      replaced by its own expanded definition, up to `maxTreeSize + 1`. Reading through the
      definition charges this against the allowance of a goal or assumption, which starts at
      `maxTreeSize`; a definition larger than what is left is not read. -/
  expandedSize : Nat

/-- `n` minus the number of nodes of the tree of `e` with each variable that has a definition
    in `defs` counted as its `Definition.expandedSize`, or `0` when that is at least `n`. It
    visits at most `n` nodes, however much `e` shares. -/
def expandedLeft (defs : Std.HashMap CoreIdent Definition) : Nat → Expression.Expr → Nat
  | 0, _ => 0
  | n + 1, .fvar _ x _ =>
    match defs.get? x with
    | some df => (n + 1) - df.expandedSize
    | none => n
  | n + 1, .const .. | n + 1, .op .. | n + 1, .bvar .. => n
  | n + 1, .abs _ _ _ b | n + 1, .quant _ _ _ _ _ b => expandedLeft defs n b
  | n + 1, .app _ a b | n + 1, .eq _ a b => expandedLeft defs (expandedLeft defs n a) b
  | n + 1, .ite _ c a b => expandedLeft defs (expandedLeft defs (expandedLeft defs n c) a) b

/-- Whether the tree of `e` has more than `maxTreeSize` nodes. -/
def tooLarge (e : Expression.Expr) : Bool :=
  expandedLeft {} (maxTreeSize + 1) e == 0

/-- A conditional fact: wherever `cond` has the value `value`, `concl` holds. -/
structure CondFact where
  cond : Expression.Expr
  value : Bool
  concl : Expression.Expr

/-- What holds on a path. No fact mentions a loose bound variable. -/
structure Facts where
  /-- The values of variables and terms, keyed by the hash of the term (`LExpr.hashExpr`):
      `(t, some v)` says that `t` has the value `v`, and `(t, none)` that assumptions gave `t`
      two different values, of which none is kept. A value mentions no bound variable, and a
      term mentions one only when it is a quantified formula with no loose bound variable. -/
  values : Std.HashMap UInt64 (List (Expression.Expr × Option Expression.Expr)) := {}
  /-- The variables' definitions. -/
  defs : Std.HashMap CoreIdent Definition := {}
  /-- The conditional facts (`CondFact`), keyed by the hash of their condition, so that a
      literal finds the conditional facts whose condition it is. -/
  condRwrs : Std.HashMap UInt64 (List CondFact) := {}
  /-- Some assumption on the path rewrote to `false`. -/
  dead : Bool := false

/-- No facts. -/
def Facts.empty : Facts := {}

/-- The facts at a point no state reaches, such as the statement after an `exit`: every goal
    holds there, and the join with any `f` is `f`. -/
def Facts.unreachable : Facts := { dead := true }

/-- Whether an assumption on the path rewrote to `false`, so that no state reaches the
    point. -/
def Facts.isDead (fs : Facts) : Bool := fs.dead

/-- `some l`, or `none` when `l` is empty. -/
@[inline] def nonEmpty {α : Type} (l : List α) : Option (List α) :=
  if l.isEmpty then none else some l

/-- The value `fs` records for the term `e`, whose hash is `h`. -/
def Facts.value? (fs : Facts) (e : Expression.Expr) (h : UInt64) : Option Expression.Expr :=
  (fs.values.get? h).bind fun b => (b.find? (·.1.beqIgnoringMetadata e)).bind (·.2)

/-- `fs` with the value `v` of the term `t`. A term given two different values keeps
    none. -/
def Facts.insertValue (fs : Facts) (t v : Expression.Expr) : Facts :=
  let h := LExpr.hashExpr t
  let b := fs.values.getD h []
  match b.find? (·.1.beqIgnoringMetadata t) with
  | none => { fs with values := fs.values.insert h ((t, some v) :: b) }
  | some (_, some w) =>
    if w.beqIgnoringMetadata v then fs else
    let b' := b.map fun (k, x) => if k.beqIgnoringMetadata t then (k, none) else (k, x)
    { fs with values := fs.values.insert h b' }
  | some (_, none) => fs

/-- `fs` without the facts that mention one of `xs`: the facts a write to `xs` may falsify. A
    fact mentions no loose bound variable, so a bound variable named like one of `xs` is not
    affected. -/
def Facts.forget (fs : Facts) (xs : List CoreIdent) : Facts :=
  if xs.isEmpty then fs else
  let xs' : Std.HashSet CoreIdent := Std.HashSet.ofList xs
  let mentions (e : Expression.Expr) : Bool :=
    (Imperative.HasFvars.getFvars (P := Expression) e).any (xs'.contains ·)
  { fs with
    values := fs.values.filterMap fun _ b =>
      nonEmpty (b.filter fun (k, v) => !mentions k && !(v.map mentions).getD false)
    defs := fs.defs.filter fun x d =>
      !xs'.contains x && !mentions d.written && !mentions d.simplified
    condRwrs := fs.condRwrs.filterMap fun _ b =>
      nonEmpty (b.filter fun c => !mentions c.cond && !mentions c.concl) }

/-- The entries of the buckets `f` that `g` has too, by `same`. -/
def joinBuckets {α : Type} (same : α → α → Bool) (f g : Std.HashMap UInt64 (List α)) :
    Std.HashMap UInt64 (List α) :=
  f.filterMap fun h b =>
    let b' := g.getD h []
    nonEmpty (b.filter fun x => b'.any (same x))

/-- The facts that hold wherever `f` holds or `g` holds: what both record, with the same
    right-hand side up to metadata. A dead side holds nowhere, so the join is the other
    side. -/
def Facts.join (f g : Facts) : Facts :=
  if f.dead then g else if g.dead then f else
  { values := joinBuckets (fun (k, v) (k', v') =>
      match v, v' with
      | some v, some v' => k.beqIgnoringMetadataFast k' && v.beqIgnoringMetadataFast v'
      | _, _ => false) f.values g.values
    defs := f.defs.filter fun x d =>
      match g.defs.get? x with
      | some d' => d.written.beqIgnoringMetadataFast d'.written &&
          d.simplified.beqIgnoringMetadataFast d'.simplified
      | none => false
    condRwrs := joinBuckets (fun a b => a.value == b.value &&
      a.cond.beqIgnoringMetadataFast b.cond && a.concl.beqIgnoringMetadataFast b.concl)
      f.condRwrs g.condRwrs }

/-! ## The context of a subterm -/

/-- A literal learned from a condition passed on the way down into a goal: `key` has the value
    `val`, and `hash` is the hash of `key`. `bound` says whether it mentions a loose bound
    variable; such a fact holds only under the binders it was learned under. -/
structure InnerFact where
  key : Expression.Expr
  hash : UInt64
  val : Expression.Expr
  bound : Bool

/-- The facts in force at a subterm of a goal: the path's facts and the inner facts. -/
structure Context where
  facts : Facts
  inner : List InnerFact := []

/-- The value the context gives the term `e`, whose hash is `h`. -/
def Context.lookup (ctx : Context) (e : Expression.Expr) (h : UInt64) :
    Option Expression.Expr :=
  match ctx.inner.find? (fun f => f.hash == h && f.key.beqIgnoringMetadataFast e) with
  | some f => some f.val
  | none => ctx.facts.value? e h

/-- `Context.lookup` on `t`, or, for an equation `a == b` whose sides have the hashes
    `sides`, on `b == a`. -/
def Context.lookupH (ctx : Context) (t : HExpr) (sides : Option (UInt64 × UInt64)) :
    Option Expression.Expr :=
  match ctx.lookup t.e t.h.1 with
  | some v => some v
  | none =>
    match t.e, sides with
    | .eq m a b, some (ha, hb) => ctx.lookup (.eq m b a) (LExpr.hashEqExpr hb ha)
    | _, _ => none

/-- `ctx` with the literals `ls` as inner facts. -/
def Context.addInner (ctx : Context) (ls : List (Expression.Expr × Expression.Expr)) :
    Context :=
  { ctx with
    inner := ls.foldl (init := ctx.inner) fun acc (k, v) =>
      ⟨k, LExpr.hashExpr k, v, !(LExpr.lcAt 0 k && LExpr.lcAt 0 v)⟩ :: acc }

/-- `ctx` under one more binder: without the inner facts that mention a loose bound
    variable. -/
def Context.underBinder (ctx : Context) : Context :=
  { ctx with inner := ctx.inner.filter (!·.bound) }

/-- Whether a fact gives `e` the value `b`. -/
@[inline] def Context.gives (ctx : Context) (e : Expression.Expr) (b : Bool) : Bool :=
  ((ctx.lookup e (LExpr.hashExpr e)).bind (·.denoteBool)) == some b

/-- Whether the context gives `e` the value `b` without rewriting: `e` is the literal `b`, a
    fact gives it `b`, or it is a negation, conjunction or disjunction whose operands the
    context settles that way. -/
def directValue (env : Env σ) (ctx : Context) (b : Bool) (e : Expression.Expr) : Bool :=
  match e.denoteBool with
  | some c => c == b
  | none =>
    ctx.gives e b ||
    match _h : env.conn? e, b with
    | some (.not a), _ => directValue env ctx (!b) a
    | some (.bin .and x y), true | some (.bin .or x y), false =>
      directValue env ctx b x && directValue env ctx b y
    | some (.bin .and x y), false | some (.bin .or x y), true =>
      directValue env ctx b x || directValue env ctx b y
    | _, _ => false
termination_by sizeOf e
decreasing_by all_goals (apply Conn.of?_lt _h; simp [Conn.operands])

/-! ## Literals -/

/-- The literals `e` gives when it has the value `polarity`: each pair `(t, v)` says that `t`
    has the value `v`. For example, `literals (a ∧ ¬b) true = [(a, true), (b, false)]`.

    * A conjunction with `polarity = true` gives the literals of both operands, as does a
      disjunction or an implication with `polarity = false` (with the polarities that make
      it false); `ite a b false` with `polarity = true` gives itself and the literals of `a`
      and `b`.
    * A negation, and `ite a false true`, give the literals of the operand with the other
      polarity.
    * An equation with `polarity = true` and a value or a constructor application on one side
      (`EqualitySimplification.orient`) gives that side as the value of the other side, and
      itself.
    * Any other Boolean term gives itself. Constants and abstractions give nothing. -/
def literals (env : Env σ) (e : Expression.Expr) (polarity : Bool) :
    List (Expression.Expr × Expression.Expr) :=
  match e with
  | .const .. | .abs .. | .bvar .. => []
  | .ite _ a b f =>
    if polarity && f.isFalse then (e, boolLit true) :: (literals env a true ++ literals env b true)
    else if b.isFalse && f.isTrue then literals env a (!polarity)
    else [(e, boolLit polarity)]
  | .eq _ l r =>
    if polarity then
      match EqualitySimplification.orient env.functions l r l r with
      | some (lhs, _, rhs) => [(lhs, rhs), (e, boolLit true)]
      | none => [(e, boolLit true)]
    else [(e, boolLit false)]
  | e' =>
    match _h : env.conn? e', polarity with
    | some (.not a), _ => literals env a (!polarity)
    | some (.bin .and a b), true => literals env a true ++ literals env b true
    | some (.bin .or a b), false => literals env a false ++ literals env b false
    | some (.bin .implies a b), false => literals env a true ++ literals env b false
    | _, _ => [(e, boolLit polarity)]
termination_by sizeOf e
decreasing_by
  all_goals first
    | (apply Conn.of?_lt _h; simp [Conn.operands])
    | (simp only [LExpr.ite.sizeOf_spec]; omega)

/-- The variable of a literal `x ↦ true` or `x ↦ false`, with the value. -/
def boolVarLit? : Expression.Expr × Expression.Expr → Option (CoreIdent × Bool)
  | (.fvar _ x _, .const _ (.boolConst b)) => some (x, b)
  | _ => none

/-! ## The rewriter -/

/-- The rewriter's state for one goal or assumption. -/
structure St where
  /-- Steps left (`maxSteps`). -/
  steps : Nat := maxSteps
  /-- Nodes of expanded definitions that may still be read (`Definition.expandedSize`). -/
  allowance : Nat := maxTreeSize
  /-- How many more definitions may be read through in a row. -/
  readDepth : Nat := defDepth
  /-- Whether the steps ran out. -/
  exhausted : Bool := false

/-- Mark the steps as run out and give `t` back. -/
@[inline] def giveUp {α : Type} (t : α) : StateM St α := do
  modify fun st => { st with exhausted := true }
  return t

/-- Spend one step; `false` when none is left. -/
@[inline] def spend : StateM St Bool := modifyGet fun st =>
  if st.steps == 0 then (false, { st with exhausted := true })
  else (true, { st with steps := st.steps - 1 })

/-- The backchaining level the hypotheses of `r` are discharged at, when `r` fires at level
    `d`. -/
@[inline] def CondRule.dischargeDepth (r : CondRule σ) (d : Nat) : Nat :=
  match r.hypDepth with
  | some c => min d c
  | none => d

/-- The definition of the first operand of `e` at one of the positions `ps` that is a variable
    with a definition, and a way to put a term in its place. -/
def definedOperand (ctx : Context) (e : Expression.Expr) (ps : List Nat) :
    Option (Definition × (Expression.Expr → Expression.Expr)) :=
  let ops := operands e
  ps.findSome? fun i =>
    match (ops[i]? : Option Expression.Expr) with
    | some (.fvar _ x _) => (ctx.facts.defs.get? x).map (·, setOperand e i)
    | _ => none

/-- The terms of `known` rewritten under the condition `c` having the value `polarity`, with
    their operands: the branch of an `ite c a b` that `polarity` selects, and the second
    operand of `c ∧ x` and `c ⇒ x` (for `true`) or of `c ∨ x` (for `false`). A rule that moves
    such a term under the same condition, such as `ite c x false → c ∧ x`, need not rewrite it
    again. -/
def knownUnder (env : Env σ) (known : List Expression.Expr) (c : Expression.Expr)
    (polarity : Bool) : List Expression.Expr :=
  known.flatMap fun k =>
    let under : Option Expression.Expr :=
      match k with
      | .ite _ c' a b => if c'.beqIgnoringMetadataFast c then some (if polarity then a else b)
        else none
      | _ =>
        match env.conn? k, polarity with
        | some (.bin .and c' x), true | some (.bin .implies c' x), true
        | some (.bin .or c' x), false =>
          if c'.beqIgnoringMetadataFast c then some x else none
        | _, _ => none
    match under with
    | some x => x :: operands x
    | none => []

mutual

/-- Rewrite `e` under `ctx`, children first, at backchaining level `d` (hypotheses of a rule
    applied here are discharged at level `d - 1`). A subterm equal to one of `known`, terms
    already rewritten under `ctx`, is kept as it is (`knownUnder` says which stay known under
    a condition). `n` bounds the recursion; running out of it, like running out of steps,
    leaves the term as it is. -/
def rw (env : Env σ) : Nat → Nat → List Expression.Expr → Context → Expression.Expr →
    StateM St HExpr
  | 0, _, _, _, e => giveUp (HExpr.of e)
  | n + 1, d, known, ctx, e => do
    if known.any (·.beqIgnoringMetadataFast e) then return HExpr.of e
    if !(← spend) then return HExpr.of e
    match e with
    | .const .. | .bvar .. => return HExpr.of e
    | .op .. => node env n d ctx (HExpr.of e) none
    | .fvar _ x _ => var env n d ctx e x
    | .abs m name ty body => do
      let b ← rw env n d known ctx.underBinder body
      return HExpr.abs m name ty b
    | .quant m k name ty tr body => do
      let b ← rw env n d known ctx.underBinder body
      node env n d ctx (HExpr.quant m k name ty tr b) none
    | .ite m c a b => do
      let c' ← rw env n d known ctx c
      match c'.e with
      | .const _ (.boolConst true) => rw env n d known ctx a
      | .const _ (.boolConst false) => rw env n d known ctx b
      | _ =>
        let ctxT := ctx.addInner (← literalsThrough env n d ctx 1 c'.e true)
        let a' ← rw env n d (knownUnder env known c'.e true) ctxT a
        let ctxF := ctx.addInner (← literalsThrough env n d ctx 1 c'.e false)
        let b' ← rw env n d (knownUnder env known c'.e false) ctxF b
        node env n d ctx (HExpr.ite m c' a' b') none
    | .eq m a b => do
      let a' ← rw env n d known ctx a
      let b' ← rw env n d known ctx b
      node env n d ctx (HExpr.eq m a' b') (some (a'.h.1, b'.h.1))
    | .app m fn arg =>
      match env.conn? e, fn, spine? e [] with
      | some (.bin k a b), .app m1 opE _, _ =>
        connective env n d known ctx (HExpr.of opE) k m1 a m b
      | _, _, some (opE, args) => do
        let args' ← args.mapM fun (ma, a) => do return (ma, ← rw env n d known ctx a)
        node env n d ctx (HExpr.applyAll (HExpr.of opE) args') none
      | _, _, none => do
        let fn' ← rw env n d known ctx fn
        let arg' ← rw env n d known ctx arg
        node env n d ctx (HExpr.app m fn' arg') none

/-- Rewrite the binary connective `k` (the operator `opH`) applied to `a` and `b`: `b` under
    the context `a` gives it, `a` true for `∧` and `⇒`, false for `∨`. When `a` alone settles
    the value (`false ∧ b`, `false ⇒ b`, `true ∨ b`), the result is that value and `b` is not
    rewritten. -/
def connective (env : Env σ) : Nat → Nat → List Expression.Expr → Context → HExpr →
    BinConn → ExprSourceLoc → Expression.Expr → ExprSourceLoc → Expression.Expr →
    StateM St HExpr
  | 0, _, _, _, opH, _, m1, a, m2, b => giveUp (HExpr.of (.app m2 (.app m1 opH.e a) b))
  | n + 1, d, known, ctx, opH, k, m1, a, m2, b => do
    let a' ← rw env n d known ctx a
    match k, a'.e with
    | .and, .const _ (.boolConst false) => return HExpr.of (boolLit false)
    | .implies, .const _ (.boolConst false) => return HExpr.of (boolLit true)
    | .or, .const _ (.boolConst true) => return HExpr.of (boolLit true)
    | _, _ => do
      let pol := !(k matches .or)
      let ctxA := ctx.addInner (← literalsThrough env n d ctx 1 a'.e pol)
      let b' ← rw env n d (knownUnder env known a'.e pol) ctxA b
      node env n d ctx (HExpr.app m2 (HExpr.app m1 opH a') b') none

/-- Rewrite the variable `e`, named `x`: its value by the context, or, for a Boolean variable
    whose definition rewrites to a literal, that literal. -/
def var (env : Env σ) : Nat → Nat → Context → Expression.Expr → CoreIdent → StateM St HExpr
  | 0, _, _, e, _ => giveUp (HExpr.of e)
  | n + 1, d, ctx, e, x => do
    let t := HExpr.of e
    match ctx.lookup t.e t.h.1 with
    | some v => return HExpr.of v
    | none =>
      match isBoolVar e, ctx.facts.defs.get? x with
      | true, some df =>
        if isConst df.simplified then return HExpr.of df.simplified
        match ← readDef env n d ctx df id with
        | some r => return (if isConst r.e then r else t)
        | none => return t
      | _, _ => return t

/-- The node `t`, whose children are rewritten: its value by the context, else the first rule
    that fires (`tryRules`), else a read through a definition (`readThrough`). `sides` are the
    hashes of the sides of an equation. -/
def node (env : Env σ) : Nat → Nat → Context → HExpr → Option (UInt64 × UInt64) →
    StateM St HExpr
  | 0, _, _, t, _ => giveUp t
  | n + 1, d, ctx, t, sides => do
    match ctx.lookupH t sides with
    | some v => return HExpr.of v
    | none =>
      let rules := env.rulesFor t.e
      if rules.isEmpty then return t
      match ← tryRules env n d ctx t.e rules with
      | some r => return r
      | none => readThrough env n d ctx t rules

/-- The first of `rules` that fires on `e`: it applies, and each of its hypotheses is
    discharged. The result is its right-hand side, rewritten. -/
def tryRules (env : Env σ) : Nat → Nat → Context → Expression.Expr → List (CondRule σ) →
    StateM St (Option HExpr)
  | 0, _, _, _, _ => giveUp none
  | _, _, _, _, [] => return none
  | n + 1, d, ctx, e, r :: rs => do
    if !(← spend) then return none
    match r.apply env.theories e with
    | none => tryRules env n d ctx e rs
    | some (rhs, hs) =>
      let known := e :: pieces e
      if ← discharge env n (r.dischargeDepth d) known ctx hs then
        return some (← rw env n d known ctx rhs)
      else tryRules env n d ctx e rs

/-- Whether every hypothesis of `hs` holds, at backchaining level `k`: at level `0` by the
    facts directly (`directValue`), else by rewriting to `true` at level `k - 1`. Stops at the
    first hypothesis that does not hold. -/
def discharge (env : Env σ) : Nat → Nat → List Expression.Expr → Context →
    List Expression.Expr → StateM St Bool
  | 0, _, _, _, _ => giveUp false
  | _, _, _, _, [] => return true
  | n + 1, k, known, ctx, h :: hs => do
    let ok ← match k with
      | 0 => pure (directValue env ctx true h)
      | k' + 1 => do
        let r ← rw env n k' known ctx h
        pure r.e.isTrue
    if ok then discharge env n k known ctx hs else return false

/-- The node `t` rewritten with the definition of an operand whose head one of `rules` reads
    in its place, when there is one and the allowance covers it. For a Boolean node, `t` itself
    unless the result is a literal. -/
def readThrough (env : Env σ) : Nat → Nat → Context → HExpr → List (CondRule σ) →
    StateM St HExpr
  | 0, _, _, t, _ => giveUp t
  | n + 1, d, ctx, t, rules =>
    let ps := (rules.flatMap (·.needsHead env.theories t.e)).eraseDups
    match definedOperand ctx t.e ps with
    | none => return t
    | some (df, put) => do
      match ← readDef env n d ctx df put with
      | some r => return (if isBoolNode t.e && !isConst r.e then t else r)
      | none => return t

/-- `put` applied to the simplified definition `df`, rewritten, when the allowance covers
    `df.expandedSize` and fewer than `defDepth` definitions are being read through. Charges
    the allowance. -/
def readDef (env : Env σ) : Nat → Nat → Context → Definition →
    (Expression.Expr → Expression.Expr) → StateM St (Option HExpr)
  | 0, _, _, _, _ => giveUp none
  | n + 1, d, ctx, df, put => do
    let st ← get
    if st.readDepth == 0 || st.allowance < df.expandedSize then return none
    set { st with allowance := st.allowance - df.expandedSize, readDepth := st.readDepth - 1 }
    let r ← rw env n d [] ctx (put df.simplified)
    modify fun s => { s with readDepth := st.readDepth }
    return some r

/-- The literals of `e` having the value `polarity`, with those of the definitions of the
    Boolean variables they give a value, rewritten, up to `depth` definitions in a row. -/
def literalsThrough (env : Env σ) : Nat → Nat → Context → Nat → Expression.Expr → Bool →
    StateM St (List (Expression.Expr × Expression.Expr))
  | 0, _, _, _, _, _ => giveUp []
  | _ + 1, _, _, 0, e, polarity => pure (literals env e polarity)
  | n + 1, d, ctx, depth + 1, e, polarity => do
    let ls := literals env e polarity
    let extra ← ls.foldlM (init := []) fun acc l =>
      match boolVarLit? l with
      | some (x, b) =>
        match ctx.facts.defs.get? x with
        | some df => do
          match ← readDef env n d ctx df id with
          | some r => pure ((← literalsThrough env n d ctx depth r.e b) ++ acc)
          | none => pure acc
        | none => pure acc
      | none => pure acc
    return ls ++ extra

end

/-- What rewriting one term gave besides the result. -/
structure RewriteStats where
  /-- The steps ran out, so part of the term may be left as it was. -/
  exhausted : Bool := false
  /-- The term's tree is larger than `maxTreeSize`, so it was left as it is. -/
  tooLarge : Bool := false

/-- `e` rewritten under `fs`: a term with the value of `e` in every state where `fs` holds. A
    term whose tree is larger than `maxTreeSize` is left as it is. -/
def rewrite (env : Env σ) (fs : Facts) (e : Expression.Expr) : Expression.Expr × RewriteStats :=
  if !env.enabled then (e, {})
  else if tooLarge e then (e, { tooLarge := true })
  else
    let (r, st) := (rw env maxSteps maxBackchain [] { facts := fs } e).run {}
    (r.e, { exhausted := st.exhausted })

/-- Whether `e` holds wherever `fs` holds, by rewriting: the path is dead, or `e` rewrites to
    `true`. -/
def closes (env : Env σ) (fs : Facts) (e : Expression.Expr) : Bool :=
  fs.dead || (rewrite env fs e).1.isTrue

/-! ## Learning assumptions -/

/-- The definition the assumption `e` states, with the side of the equation it is on (`true`
    for the right side): `e` is `x == d` or `d == x` for a variable `x` without a definition,
    where `d` does not mention `x` or a bound variable and is not a value or a constructor
    application. In an equation between two variables, the left one is defined by the right
    one, or, when the left one has a definition, the right one by the left one; not when the
    other's definitions lead back to it. -/
def definition? (env : Env σ) (fs : Facts) (e : Expression.Expr) :
    Option (CoreIdent × Expression.Expr × Bool) :=
  let free (x : CoreIdent) : Bool := !fs.defs.contains x
  let mentions (d : Expression.Expr) (x : CoreIdent) : Bool :=
    (Imperative.HasFvars.getFvars (P := Expression) d).contains x
  -- Whether the definitions of `y`, read while they are variables, mention `x`.
  let reaches (y x : CoreIdent) : Bool :=
    (List.range defDepth).foldl (init := (some y, false)) (fun (cur, found) _ =>
      if found then (cur, found) else
      match cur with
      | some c =>
        if c == x then (none, true) else
        match fs.defs.get? c with
        | some df =>
          match df.written with
          | .fvar _ z _ => (some z, false)
          | w => (none, mentions w x)
        | none => (none, false)
      | none => (none, false)) |>.2
  let side (lhs d : Expression.Expr) (right : Bool) : Option (CoreIdent × Expression.Expr × Bool) :=
    match lhs with
    | .fvar _ x _ =>
      if free x && !d.hasBVar && !EqualitySimplification.isReplacement env.functions d
          && !mentions d x then some (x, d, right)
      else none
    | _ => none
  match e with
  | .eq _ l@(.fvar _ x _) r@(.fvar _ y _) =>
    if x == y then none else
    if free x && !reaches y x then some (x, r, true)
    else if free y && !reaches x y then some (y, l, false)
    else none
  | .eq _ l r => side l r true <|> side r l false
  | _ => none

/-- `fs` with the definition `x := d`, `d` rewritten being `d'`. -/
def Facts.addDefinition (fs : Facts) (x : CoreIdent) (d d' : Expression.Expr) : Facts :=
  let expandedSize := (maxTreeSize + 1) - expandedLeft fs.defs (maxTreeSize + 1) d
  { fs with defs := fs.defs.insert x { written := d, simplified := d', expandedSize } }

/-- The conditional facts the literal `(k, v)` gives: `a ⇒ d` true gives `d` where `a` is
    true, and `a ∨ d` true gives each operand where the other is false. -/
def condFacts (env : Env σ) : Expression.Expr × Expression.Expr → List CondFact
  | (k, .const _ (.boolConst true)) =>
    match env.conn? k with
    | some (.bin .implies a d) => [⟨a, true, d⟩]
    | some (.bin .or a d) => [⟨a, false, d⟩, ⟨d, false, a⟩]
    | _ => []
  | _ => []

/-- `fs` with the literals `ls` recorded. A literal is not recorded when its value mentions a
    bound variable, or when its term does and is not a quantified formula with no loose bound
    variable. -/
def Facts.addLiterals (env : Env σ) (fs : Facts) (ls : List (Expression.Expr × Expression.Expr)) :
    Facts :=
  ls.foldl (init := fs) fun fs (k, v) =>
    if v.hasBVar || (k.hasBVar && !(k matches .quant .. && LExpr.lcAt 0 k)) then fs
    else
      let fs := fs.insertValue k v
      (condFacts env (k, v)).foldl (init := fs) fun (fs : Facts) (c : CondFact) =>
        if c.cond.hasBVar || c.concl.hasBVar then fs else
        let h := LExpr.hashExpr c.cond
        { fs with condRwrs := fs.condRwrs.insert h (c :: fs.condRwrs.getD h []) }

/-- The conclusions of the conditional facts of `fs` whose condition one of the literals `ls`
    meets. Each literal looks up only the conditional facts filed under the hash of its term,
    so the work is the number of literals times the size of the lists they find. For example,
    with the conditional fact "where `p` is `true`, `q` holds" (from `p ⇒ q`), the literal
    `p ↦ true` gives `[q]`. -/
def Facts.consequences (fs : Facts) (ls : List (Expression.Expr × Expression.Expr)) :
    List Expression.Expr :=
  ls.foldl (init := []) fun acc (k, v) =>
    match v with
    | .const _ (.boolConst b) =>
      (fs.condRwrs.getD (LExpr.hashExpr k) []).foldl (init := acc) fun acc c =>
        if c.value == b && c.cond.beqIgnoringMetadata k then c.concl :: acc else acc
    | _ => acc

/-- Learn the assumption `e` under `fs`: the facts with the definition `e` states, and the
    literals of `e` rewritten; `none` when `e` rewrites to `false`. -/
def learn (env : Env σ) (fs : Facts) (e : Expression.Expr) :
    StateM St (Option (Facts × List (Expression.Expr × Expression.Expr))) := do
  let ctx : Context := { facts := fs }
  let (e', fs1) ← match e, definition? env fs e with
    | .eq m l r, some (x, d, right) => do
      let l' ← rw env maxSteps maxBackchain [] ctx l
      let r' ← rw env maxSteps maxBackchain [] ctx r
      let e' ← node env maxSteps maxBackchain ctx (HExpr.eq m l' r') (some (l'.h.1, r'.h.1))
      pure (e', fs.addDefinition x d (if right then r'.e else l'.e))
    | _, _ => do
      let e' ← rw env maxSteps maxBackchain [] ctx e
      pure (e', fs)
  if e'.e.isFalse then return none
  let ls ← literalsThrough env maxSteps maxBackchain { facts := fs1 } defDepth e'.e true
  return some (fs1, ls)

/-- `Facts.assume`, following at most `n` conditional facts in a row. -/
def Facts.assumeWith (env : Env σ) : Nat → Facts → Expression.Expr → Facts
  | 0, fs, _ => fs
  | n + 1, fs, e =>
    if fs.dead then fs else
    match (learn env fs e).run' {} with
    | none => Facts.unreachable
    | some (fs1, ls) =>
      -- Read before the literals are added, so that `fs1` is not shared when they are.
      let ds := fs1.consequences ls
      ds.foldl (init := fs1.addLiterals env ls) fun fs d => Facts.assumeWith env n fs d

/-- The facts after `assume e` where `fs` holds, as described in the module documentation:
    the definition `e` states, then `e` rewritten under `fs`, split into literals, which are
    recorded; `false` marks the path dead. An assumption whose tree is larger than
    `maxTreeSize` gives nothing. -/
def Facts.assume (env : Env σ) (fs : Facts) (e : Expression.Expr) : Facts :=
  if env.enabled && !tooLarge e then Facts.assumeWith env defDepth fs e else fs

end -- public section

end Core.ContextualRewrite
