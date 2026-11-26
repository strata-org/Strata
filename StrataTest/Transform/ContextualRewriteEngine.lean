/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.ContextualRewrite.Rules

meta section

/-! # Contextual rewriting of goals

Each rule of `Core.ContextualRewrite` on a goal it rewrites to `true`, and on a closely related
goal it must leave unproved; the facts domain (`assume`, `forget`, `join`); and backchaining.
Goals are built by hand over a datatype `T = A(a : int) | B(b : int) | C()`, typed as the type
checker annotates them. -/

namespace Core.ContextualRewrite.Tests

open Lambda hiding Env

private def m : ExprSourceLoc := coreLoc

private def tT : LMonoTy := .tcons "T" []
private def mapTy (k v : LMonoTy) : LMonoTy := .tcons "Map" [k, v]
private def seqTy (a : LMonoTy) : LMonoTy := .tcons "Sequence" [a]

private def dtT : LDatatype Unit :=
  { name := "T", typeArgs := [],
    constrs := [
      { name := ⟨"A", ()⟩, args := [(⟨"a", ()⟩, .int)], testerName := "T..isA" },
      { name := ⟨"B", ()⟩, args := [(⟨"b", ()⟩, .int)], testerName := "T..isB" },
      { name := ⟨"C", ()⟩, args := [], testerName := "T..isC" }],
    constrs_ne := rfl }

/-- A datatype with two constructors, `Res = Ok(v : int) | Error(e : int)`. -/
private def tRes : LMonoTy := .tcons "Res" []
private def dtRes : LDatatype Unit :=
  { name := "Res", typeArgs := [],
    constrs := [
      { name := ⟨"Ok", ()⟩, args := [(⟨"v", ()⟩, .int)], testerName := "Res..isOk" },
      { name := ⟨"Error", ()⟩, args := [(⟨"e", ()⟩, .int)], testerName := "Res..isError" }],
    constrs_ne := rfl }

/-- A datatype with one constructor, `U = MkU(u : int)`. -/
private def tU : LMonoTy := .tcons "U" []
private def dtU : LDatatype Unit :=
  { name := "U", typeArgs := [],
    constrs := [{ name := ⟨"MkU", ()⟩, args := [(⟨"u", ()⟩, .int)], testerName := "U..isMkU" }],
    constrs_ne := rfl }

/-- The names of the copies of Core's map and sequence functions the goals below use. -/
private def monoNames : List (String × String) :=
  [("select", "$__mono#select#int#int"), ("update", "$__mono#update#int#int"),
    ("mapConst", "$__mono#mapConst#int#int"), ("Sequence.length", "$__mono#Sequence.length#int"),
    ("Sequence.build", "$__mono#Sequence.build#int"),
    ("Sequence.empty", "$__mono#Sequence.empty#int"),
    ("Sequence.select!", "$__mono#Sequence.select!#int")]

/-- Copies of Core's map and sequence functions at `int`, under the mangled names the goals
    below use, as monomorphization adds them to the function table: marked as copies, with
    their signatures and axioms instantiated and their axioms reading the copies. They have no
    evaluators, so that the evaluation rule leaves the goals to the other rules, except the
    length, whose evaluator gives the length of a sequence literal. -/
private def monoFuncs : Array (LFunc CoreLParams) :=
  let S := tySubstOf [("k", .int), ("v", .int), ("a", .int)]
  (monoNames.filterMap fun (b, n) =>
    (Core.Factory.get? b).map fun f =>
      { f with name := ⟨n, ()⟩, typeArgs := [],
               inputs := f.inputs.map fun (x, t) => (x, t.subst S),
               output := f.output.subst S,
               axioms := f.axioms.map (instAx S monoNames),
               attr := f.attr.push (.monoCopyOf b),
               concreteEval := if b == "Sequence.length" then f.concreteEval else none }).toArray

/-- An uninterpreted predicate `g : int → bool`. -/
private def gFunc : LFunc CoreLParams :=
  { name := ⟨"g", ()⟩, inputs := [(⟨"n", ()⟩, .int)], output := .bool }

private def factory : Lambda.Factory CoreLParams :=
  let parts : List (Except _ (Lambda.Factory CoreLParams)) :=
    [genBlockFactory (T := CoreLParams) [dtT], genBlockFactory (T := CoreLParams) [dtU],
      genBlockFactory (T := CoreLParams) [dtRes], .ok (Lambda.Factory.ofArray monoFuncs),
      .ok (Lambda.Factory.ofArray #[gFunc])]
  parts.foldl (init := Core.Factory) fun F p =>
    match p with
    | .ok f => match F.addFactory f with
      | .ok F => F
      | .error _ => F
    | .error _ => F

private def env : Env Theories := Env.ofFactory factory [dtT, dtU, dtRes]

-- The function table has the operators the rules build.
#guard env.enabled

/-! ## Building terms -/

private def var (n : String) (ty : LMonoTy) : Expression.Expr := .fvar m ⟨n, ()⟩ (some ty)
private def op (n : String) (ty : LMonoTy) : Expression.Expr := .op m ⟨n, ()⟩ (some ty)
private def app1 (f a : Expression.Expr) : Expression.Expr := .app m f a
private def app2 (f a b : Expression.Expr) : Expression.Expr := .app m (.app m f a) b
private def app3 (f a b c : Expression.Expr) : Expression.Expr := .app m (.app m (.app m f a) b) c
private def int (i : Int) : Expression.Expr := .intConst m i
private def tt : Expression.Expr := .boolConst m true
private def ff : Expression.Expr := .boolConst m false
private def eq (a b : Expression.Expr) : Expression.Expr := .eq m a b
private def ite (c a b : Expression.Expr) : Expression.Expr := .ite m c a b
private def and (a b : Expression.Expr) : Expression.Expr := app2 boolAndOp a b
private def or (a b : Expression.Expr) : Expression.Expr := app2 boolOrOp a b
private def imp (a b : Expression.Expr) : Expression.Expr := app2 boolImpliesOp a b
private def not (a : Expression.Expr) : Expression.Expr := app1 boolNotOp a
private def le (a b : Expression.Expr) : Expression.Expr := app2 intLeOp a b
private def lt (a b : Expression.Expr) : Expression.Expr := app2 intLtOp a b
private def add (a b : Expression.Expr) : Expression.Expr := app2 intAddOp a b

private def p := var "p" .bool
private def q := var "q" .bool
private def h := var "h" .bool
private def x := var "x" tT
private def y := var "y" .int
private def z := var "z" .int
private def i := var "i" .int
private def j := var "j" .int
/-- The uninterpreted predicate `g`. -/
private def g (e : Expression.Expr) : Expression.Expr := app1 (op "g" (.arrow .int .bool)) e

private def A (e : Expression.Expr) : Expression.Expr := app1 (op "A" (.arrow .int tT)) e
private def B (e : Expression.Expr) : Expression.Expr := app1 (op "B" (.arrow .int tT)) e
private def C : Expression.Expr := op "C" tT
private def tester (c : String) (e : Expression.Expr) : Expression.Expr :=
  app1 (op s!"T..is{c}" (.arrow tT .bool)) e
private def isA := tester "A"
private def isB := tester "B"
private def isC := tester "C"
private def selA (e : Expression.Expr) : Expression.Expr := app1 (op "T..a" (.arrow tT .int)) e
private def selB (e : Expression.Expr) : Expression.Expr := app1 (op "T..b" (.arrow tT .int)) e

/-- `select` and `update` on `Map int int`, unmangled, or mangled at `Map int int` as
    monomorphization names them when `pre` is the mangling prefix. -/
private def mii := mapTy .int .int
private def sel (pre : String := "") (mp k : Expression.Expr) : Expression.Expr :=
  app2 (op (if pre.isEmpty then "select" else pre ++ "select#int#int")
    (.arrow mii (.arrow .int .int))) mp k
private def upd (pre : String := "") (mp k v : Expression.Expr) : Expression.Expr :=
  app3 (op (if pre.isEmpty then "update" else pre ++ "update#int#int")
    (.arrow mii (.arrow .int (.arrow .int mii)))) mp k v
private def mono : String := "$__mono#"
private def mk := var "mk" mii
private def v := var "v" .int

/-- Maps keyed by `T`, for keys that are constructor applications. -/
private def mti := mapTy tT .int
private def selT (mp k : Expression.Expr) : Expression.Expr :=
  app2 (op "select" (.arrow mti (.arrow tT .int))) mp k
private def updT (mp k v : Expression.Expr) : Expression.Expr :=
  app3 (op "update" (.arrow mti (.arrow tT (.arrow .int mti)))) mp k v
private def mt := var "mt" mti

private def sqi := seqTy .int
private def len (s : Expression.Expr) : Expression.Expr :=
  app1 (op "$__mono#Sequence.length#int" (.arrow sqi .int)) s
private def build (s e : Expression.Expr) : Expression.Expr :=
  app2 (op "$__mono#Sequence.build#int" (.arrow sqi (.arrow .int sqi))) s e
private def empty : Expression.Expr := op "$__mono#Sequence.empty#int" sqi
private def sq := var "sq" sqi

/-- The facts of the assumptions `as`, learned in order. -/
private def factsOf (as : List Expression.Expr) : Facts :=
  as.foldl (Facts.assume env) Facts.empty

/-- Whether `goal` is proved from the assumptions `as`. -/
private def provedFrom (as : List Expression.Expr) (goal : Expression.Expr) : Bool :=
  closes env (factsOf as) goal

/-- Whether `goal` is proved with no facts. -/
private def proved (goal : Expression.Expr) : Bool := provedFrom [] goal

/-! ## Connectives and the context they give -/

#guard proved (or p tt)
#guard !proved (or p ff)
#guard proved (imp ff p)
#guard proved (not (not (or p (not p))))
#guard !proved (or p q)
-- `∨` assumes its first operand false in the second.
#guard proved (or p (not p))
-- `⇒` assumes its antecedent in the conclusion.
#guard proved (imp p (imp q p))
#guard !proved (imp p (imp q (and p (not q))))
-- `∧` assumes its first operand in the second.
#guard proved (not (and p (not p)))
#guard !proved (not (and p q))
-- A first operand that settles the connective, as written or once rewritten, gives its value.
#guard (rewrite env Facts.empty (and ff p)).1.isFalse
#guard (rewrite env (factsOf [not p]) (and p q)).1.isFalse
#guard proved (or tt p)
#guard provedFrom [p] (or p q)
#guard provedFrom [not p] (imp p q)

/-! ## `ite` -/

#guard proved (ite p tt tt)
#guard proved (ite tt tt p)
#guard !proved (ite p tt q)
-- The condition holds in the first branch and fails in the second.
#guard proved (ite p p (not p))
#guard !proved (ite p q (not p))
-- `ite p q false` is `p ∧ q`, and splits into both literals as an antecedent.
#guard proved (imp (ite p q ff) q)
#guard !proved (imp (ite p q tt) q)
-- `ite p false true` is `¬ p`.
#guard proved (imp (ite p ff tt) (not p))
#guard !proved (imp (ite p ff q) (not q))

/-! ## Facts -/

#guard provedFrom [g y] (g y)
#guard !provedFrom [g y] (g z)
#guard provedFrom [not (g y)] (not (g y))
#guard provedFrom [and p (g y)] (and (g y) p)
#guard !provedFrom [or p (g y)] (g y)
-- An equation with a value gives the value: the goal becomes `g(3)`, which is known.
#guard provedFrom [eq y (int 3), g (int 3)] (g y)
#guard !provedFrom [eq y z, g (int 3)] (g y)
-- An earlier assumption can make a later one false: the path is dead.
#guard provedFrom [p, not p] (g z)
#guard provedFrom [isA x, isB x] (g z)
#guard !provedFrom [p, not q] (g z)

/-! ## Datatypes -/

-- A tester or a selector on a constructor application.
#guard proved (isA (A y))
#guard proved (not (isB (A y)))
#guard !proved (isB (A y))
#guard proved (eq (selA (A y)) y)
#guard !proved (eq (selB (A y)) y)
-- A tester known true settles the others.
#guard provedFrom [isA x] (not (isB x))
#guard provedFrom [isA x] (not (isC x))
#guard !provedFrom [not (isA x)] (not (isB x))
-- The testers of all other constructors known false.
#guard provedFrom [not (isA x), not (isB x)] (isC x)
#guard !provedFrom [not (isA x)] (isC x)
#guard proved (imp (not (isA x)) (imp (not (isC x)) (isB x)))
#guard !proved (imp (not (isA x)) (isB x))
-- The tester of the only constructor of a datatype.
#guard proved (app1 (op "U..isMkU" (.arrow tU .bool)) (var "w" tU))
#guard !proved (isA x)
-- Different constructors, and injectivity.
#guard proved (not (eq (A y) (B z)))
#guard proved (not (eq (A y) C))
#guard proved (imp (eq (A y) (A z)) (eq y z))
#guard !proved (eq (A y) (A z))
#guard proved (not (eq (A (int 1)) (A (int 2))))
#guard !proved (not (eq (A y) (A (int 2))))

-- A tester's siblings are the testers of the other constructors with its signature: copies of
-- `T`'s testers at `T int`, of which the copy of `T..isB` takes another type, have only the copy
-- of `T..isC` as a sibling of the copy of `T..isA`.
private def tTInt : LMonoTy := .tcons "T" [.int]
private def testerCopy (c : String) (ty : LMonoTy) (marked : Bool := true)
    (pfx : String := "$__mono") : LFunc CoreLParams :=
  { name := ⟨s!"{pfx}#T..is{c}#int", ()⟩, inputs := [(⟨"x", ()⟩, ty)], output := .bool,
    attr := if marked then #[.monoCopyOf s!"T..is{c}"] else #[] }
private def copySiblings (marked : Bool := true) (pfx : String := "$__mono") :
    Option (List String × Bool) :=
  let F := Lambda.Factory.ofArray #[testerCopy "A" tTInt marked pfx,
    testerCopy "B" tU marked pfx, testerCopy "C" tTInt marked pfx]
  ((DatatypeEnv.ofFactory F [dtT]).testers.get? s!"{pfx}#T..isA#int").map
    fun i => (i.siblings, i.complete)
#guard copySiblings == some (["$__mono#T..isC#int"], false)
-- The same under a prefix padded past a program's names.
#guard copySiblings (pfx := "$__mono__") == some (["$__mono__#T..isC#int"], false)
-- A function named like a copy but not marked as one is not a tester.
#guard copySiblings (marked := false) == none
-- Nor is one marked as the copy of another function.
#guard ((DatatypeEnv.ofFactory (Lambda.Factory.ofArray
    #[{ testerCopy "A" tTInt with attr := #[.monoCopyOf "T..isC"] }]) [dtT]).testers.get?
      "$__mono#T..isA#int").isNone

/-! ## `ite` under an operator -/

#guard proved (isA (ite p (A (int 1)) (A y)))
-- A condition that is or becomes a literal selects its branch.
#guard proved (isA (ite tt (A (int 1)) x))
#guard provedFrom [p] (isA (ite p (A (int 1)) x))
#guard !proved (isA (ite p (A (int 1)) x))
#guard provedFrom [isA x] (isA (ite p (A (int 1)) x))
#guard proved (eq (selA (ite p (A y) (A y))) y)
#guard proved (imp p (eq (ite p y z) y))
#guard !proved (eq (ite p y z) y)
#guard proved (eq (sel "" (ite p mk mk) y) (sel "" mk y))
-- A map read moves into the branches: both give `v`.
private def mk2 := var "mk2" mii
#guard proved (eq (sel "" (ite p (upd "" mk y v) (upd "" mk2 y v)) y) v)
#guard !proved (eq (sel "" (ite p (upd "" mk y v) mk2) y) v)

/-! ## Definitions of join variables

A join gives its symbol a definition, `s == ite g a b`. -/

private def s1 := var "s1" tT
private def s2 := var "s2" tT

-- The same constructor on both sides.
#guard provedFrom [eq s1 (ite p (A (int 1)) (A y))] (isA s1)
-- Different constructors, the condition settled by an earlier assumption.
#guard provedFrom [p, eq s1 (ite p (A (int 1)) (B y))] (isA s1)
#guard provedFrom [not p, eq s1 (ite p (A (int 1)) (B y))] (isB s1)
-- Different constructors, the condition unknown.
#guard !provedFrom [eq s1 (ite p (A (int 1)) (B y))] (isA s1)
#guard !provedFrom [eq s1 (ite p (A (int 1)) (B y))] (isB s1)
-- A nested join: the definition mentions another join symbol.
#guard provedFrom [eq s1 (ite p (A (int 1)) (A y)), eq s2 (ite q s1 (A z))] (isA s2)
#guard !provedFrom [eq s1 (ite p (A (int 1)) (B y)), eq s2 (ite q s1 (A z))] (isA s2)
-- A branch that is not a constructor application, settled by a fact.
#guard provedFrom [isA x, eq s1 (ite p (A y) x)] (isA s1)
#guard !provedFrom [eq s1 (ite p (A y) x)] (isA s1)
-- A fact about the symbol still matches the goal.
#guard provedFrom [eq s1 (ite p (A y) x), isB s1] (isB s1)
-- A selector reads through the definition.
#guard provedFrom [eq s1 (ite p (A y) (A y))] (eq (selA s1) y)
-- The condition settled by the goal's own antecedent.
#guard provedFrom [eq s1 (ite p (A (int 1)) (B y))] (imp p (isA s1))
#guard !provedFrom [eq s1 (ite p (A (int 1)) (B y))] (imp q (isA s1))
-- A definition gives the literals of its simplified form: `h` simplifies to `true`.
#guard provedFrom [p, eq h (or p (g y))] h
#guard !provedFrom [eq h (or p (g y))] h
-- A Boolean variable assumed true gives the literals of its definition.
#guard provedFrom [eq h (and q (g y)), h] (g y)
#guard provedFrom [eq h (or q (g y)), not h] (not (g y))
#guard !provedFrom [eq h (and q (g y))] (g y)
-- A variable whose definition is not a constructor application is left alone.
#guard !provedFrom [eq s1 (ite p x (A y))] (isA s1)

/-! ## Map reads -/

-- The same key.
#guard proved (eq (sel "" (upd "" mk y v) y) v)
#guard proved (eq (sel mono (upd mono mk y v) y) v)
-- A read and an update of different families are not related.
#guard !proved (eq (sel "" (upd mono mk y v) y) v)
-- A function named like a copy is read as one only when it is marked as one.
#guard (MapEnv.ofFactory (Lambda.Factory.ofArray monoFuncs)).ops.get? "$__mono#select#int#int"
  == some .select
#guard ((MapEnv.ofFactory (Lambda.Factory.ofArray (monoFuncs.map ({ · with attr := #[] })))).ops
  |>.get? "$__mono#select#int#int").isNone
-- Different literal keys, or different constructors.
#guard proved (eq (sel "" (upd "" mk (int 1) v) (int 2)) (sel "" mk (int 2)))
#guard proved (eq (selT (updT mt (A y) v) C) (selT mt C))
#guard proved (eq (selT (updT mt (A (int 1)) v) (A (int 2))) (selT mt (A (int 2))))
-- Unrelated variable keys, neither known equal nor known different.
#guard !proved (eq (sel "" (upd "" mk i v) j) v)
#guard !proved (eq (sel "" (upd "" mk i v) j) (sel "" mk j))
#guard !proved (eq (selT (updT mt (A i) v) (A j)) v)
-- Keys the facts show equal or different.
#guard provedFrom [eq i j] (eq (selT (updT mt (A j) v) (A i)) v)
#guard provedFrom [not (eq i j)] (eq (sel "" (upd "" mk i v) j) (sel "" mk j))
-- A constant map.
private def mconst (e : Expression.Expr) : Expression.Expr :=
  app1 (op "$__mono#mapConst#int#int" (.arrow .int mii)) e
#guard proved (eq (sel mono (mconst v) y) v)
#guard !proved (eq (sel mono mk y) v)

/-! ## Sequence lengths -/

#guard proved (eq (len empty) (int 0))
#guard proved (eq (len (build (build empty y) z)) (int 2))
#guard proved (eq (len (build sq y)) (add (len sq) (int 1)))
#guard !proved (eq (len (build sq y)) (int 1))
#guard !proved (eq (len sq) (int 0))
-- The length of a sequence literal is read.
private def emptyLit : Expression.Expr := .const m (.sequenceConst .int #[])
#guard proved (eq (len (build emptyLit y)) (int 1))
#guard proved (eq (len (.const m (.sequenceConst .int #[.intConst 1, .intConst 2]))) (int 2))
#guard !proved (eq (len (build emptyLit y)) (int 2))
-- A length moves into the branches of an `ite`.
#guard proved (eq (len (ite p empty (build empty y))) (ite p (int 0) (int 1)))
#guard !proved (eq (len (ite p empty (build empty y))) (int 0))

/-! ## Integers -/

#guard proved (eq (add (int 1) (int 2)) (int 3))
#guard proved (le y y)
#guard proved (not (lt y y))
#guard proved (lt y (add y (int 1)))
#guard proved (le (add y (int 1)) (add y (int 2)))
#guard !proved (le (add y (int 2)) (add y (int 1)))
-- Arithmetic over different variables is left to the solver.
#guard !proved (le y z)
#guard !proved (eq (add y z) (add z y))
#guard !proved (imp (lt y z) (lt y (add z (int 1))))
-- An empty range, under a quantifier: the body is a loop-entry check.
private def gB : Expression.Expr := app1 (op "g" (.arrow .int .bool)) (.bvar m 0)
private def forallInt (body : Expression.Expr) : Expression.Expr :=
  .quant m .all "k" (some .int) (.bvar m 0) body
#guard proved (forallInt (imp (and (le (int 0) (.bvar m 0)) (lt (.bvar m 0) (len empty))) gB))
#guard !proved (forallInt (imp (and (le (int 0) (.bvar m 0)) (lt (.bvar m 0) (len sq))) gB))
#guard proved (forallInt (imp (and (le (int 1) (.bvar m 0)) (le (.bvar m 0) (int 0))) gB))
#guard !proved (forallInt (imp (and (le (int 0) (.bvar m 0)) (le (.bvar m 0) (int 0))) gB))
-- A condition that mentions a bound variable is not used as a fact.
#guard proved (forallInt (imp gB gB))
-- A selector on a constructor application with a bound variable: the evaluation rule does
-- not type check the term, the selector rule applies.
#guard proved (forallInt (eq (selA (A (.bvar m 0))) (.bvar m 0)))
#guard !proved (forallInt (imp (g y) gB))

-- A quantified fact matches a goal that is the same formula.
private def gB1 : Expression.Expr := app1 (op "g" (.arrow .int .bool)) (add (.bvar m 0) (int 1))
#guard provedFrom [forallInt gB] (forallInt gB)
#guard provedFrom [and p (forallInt gB)] (forallInt gB)
#guard !provedFrom [forallInt gB] (forallInt gB1)
#guard proved (imp (forallInt gB) (forallInt gB))
-- A join keeps a quantified fact that both sides have, and a write forgets one that mentions
-- the variable written.
#guard closes env (Facts.join (factsOf [forallInt gB]) (factsOf [p, forallInt gB])) (forallInt gB)
#guard !closes env (Facts.join (factsOf [forallInt gB]) (factsOf [p])) (forallInt gB)
#guard closes env ((factsOf [forallInt (imp (g y) gB)]).forget [⟨"z", ()⟩])
  (forallInt (imp (g y) gB))
#guard !closes env ((factsOf [forallInt (imp (g y) gB)]).forget [⟨"y", ()⟩])
  (forallInt (imp (g y) gB))

-- A definition rewritten under a literal that mentions a bound variable is not reused
-- under a nested binder, where that variable is another one. The second conjunct
-- claims `a(s1) == k2` for every `k2`, which does not hold.
private def bv (i : Nat) : Expression.Expr := .bvar m i
#guard provedFrom [eq s1 x] (forallInt (imp (eq x (A (bv 0))) (eq (selA s1) (bv 0))))
#guard !provedFrom [eq s1 x]
  (forallInt (imp (eq x (A (bv 0))) (and (eq (selA s1) (bv 0)) (forallInt (eq (selA s1) (bv 0))))))

/-! ## Implications among the facts -/

-- A literal learned later fires an implication recorded earlier.
#guard provedFrom [imp p (g y), p] (g y)
#guard provedFrom [ite p (g y) tt, p] (g y)
#guard provedFrom [or p (g y), not p] (g y)
#guard !provedFrom [imp p (g y), q] (g y)
#guard !provedFrom [imp p (g y), not p] (g y)
-- A consequent is learned as an assumption, so it can fire further implications.
#guard provedFrom [imp p q, imp q (g y), p] (g y)

/-! ## Unsafe operators are left alone -/

private def selU (s i : Expression.Expr) : Expression.Expr :=
  app2 (op "$__mono#Sequence.select!#int" (.arrow sqi (.arrow .int .int))) s i
#guard !proved (eq (selU (build sq v) (len sq)) v)

/-! ## The shape of a well-formedness lemma: `p ⇒ (isA(x) ⇒ isA(x))` -/

#guard proved (imp p (imp (isA x) (isA x)))
#guard !proved (imp p (imp (isA x) (isB x)))

/-! ## Boolean rules -/

#guard proved (and (or p (not p)) tt)
#guard !proved (and p tt)
#guard proved (not (and ff p))
#guard proved (or ff (or p (not p)))
#guard proved (imp tt (or p (not p)))
-- `a ⇒ false` is `¬a`.
#guard proved (imp (imp p ff) (not p))
#guard !proved (imp (imp p ff) p)
#guard proved (not (not (or p (not p))))
#guard proved (not ff)
#guard !proved (not tt)
#guard proved (eq (or p (not p)) tt)
#guard proved (not (eq (and p (not p)) tt))
#guard proved (eq (and p (not p)) ff)
#guard !proved (eq p ff)
#guard proved (forallInt tt)
#guard !proved (.quant m .exist "k" (some .int) (.bvar m 0) ff)

/-! ## Equality -/

#guard proved (eq (g y) (g y))
#guard !proved (eq (g y) (g z))
#guard proved (not (eq (int 1) (int 2)))
#guard !proved (not (eq y (int 2)))
#guard proved (not (eq (.strConst m "a") (.strConst m "b")))

/-! ## Evaluation

A function with a concrete evaluator applied to values is its result. -/

private def concat (a b : Expression.Expr) : Expression.Expr :=
  app2 (op "Str.Concat" (.arrow .string (.arrow .string .string))) a b
#guard proved (eq (concat (.strConst m "a") (.strConst m "b")) (.strConst m "ab"))
#guard !proved (eq (concat (var "s" .string) (.strConst m "b")) (.strConst m "ab"))
-- The operator must be annotated with its signature.
#guard !proved (eq (app2 (op "Str.Concat" (.arrow .int (.arrow .int .int)))
  (.strConst m "a") (.strConst m "b")) (.strConst m "ab"))

/-! ## The worked example

`¬isOk(o)` makes `isError(o)` true: the tester of the other constructor is known false. -/

private def o := var "o" tRes
private def isOk (e : Expression.Expr) : Expression.Expr :=
  app1 (op "Res..isOk" (.arrow tRes .bool)) e
private def isError (e : Expression.Expr) : Expression.Expr :=
  app1 (op "Res..isError" (.arrow tRes .bool)) e
private def Ok (e : Expression.Expr) : Expression.Expr := app1 (op "Ok" (.arrow .int tRes)) e
private def Error (e : Expression.Expr) : Expression.Expr := app1 (op "Error" (.arrow .int tRes)) e
#guard provedFrom [not (isOk o)] (isError o)
#guard !provedFrom [] (isError o)
#guard provedFrom [isOk o] (not (isError o))
-- With a definition: the tester reads through it.
private def r := var "r" tRes
#guard provedFrom [eq r (ite p (Ok (int 1)) (Error (int 2))), p] (isOk r)
#guard !provedFrom [eq r (ite p (Ok (int 1)) (Error (int 2)))] (isOk r)

/-! ## The facts domain -/

-- `join` keeps the facts both sides record, with the same value.
#guard closes env (Facts.join (factsOf [g y, p]) (factsOf [g y, q])) (g y)
#guard !closes env (Facts.join (factsOf [g y, p]) (factsOf [g y, q])) p
#guard !closes env (Facts.join (factsOf [g y, p]) (factsOf [g y, q])) q
#guard closes env (Facts.join (factsOf [eq y (int 3)]) (factsOf [eq y (int 3)])) (eq y (int 3))
#guard !closes env (Facts.join (factsOf [eq y (int 3)]) (factsOf [eq y (int 4)])) (g (int 3))
#guard closes env
  (Facts.join (factsOf [eq y (int 3), g (int 3)]) (factsOf [eq y (int 3), g (int 3)])) (g y)
-- A definition is kept only if both sides have it.
#guard closes env (Facts.join (factsOf [p, eq s1 (ite p (A (int 1)) (B y))])
  (factsOf [p, eq s1 (ite p (A (int 1)) (B y))])) (isA s1)
#guard !closes env (Facts.join (factsOf [eq s1 (A (int 1))]) (factsOf [eq s1 (B y)])) (isA s1)
-- Conditional facts too.
#guard closes env (Facts.join (factsOf [imp p (g y)]) (factsOf [imp p (g y), q])) (imp p (g y))
#guard !(Facts.join (factsOf [imp p (g y)]) (factsOf [q])).condRwrs.contains
  (LExpr.hashExpr p)
-- A dead side joins to the other side.
#guard (factsOf [p, not p]).isDead
#guard closes env (Facts.join (factsOf [p, not p]) (factsOf [q])) q
#guard closes env (Facts.join (factsOf [q]) (factsOf [p, not p])) q
#guard !(Facts.join (factsOf [p, not p]) (factsOf [q])).isDead

-- `forget` drops the facts that mention a variable: values, definitions, conditional facts.
#guard !closes env ((factsOf [g y, p]).forget [⟨"p", ()⟩]) p
#guard closes env ((factsOf [g y, p]).forget [⟨"p", ()⟩]) (g y)
#guard !closes env ((factsOf [eq s1 (A (int 1))]).forget [⟨"s1", ()⟩]) (isA s1)
#guard !closes env ((factsOf [eq s1 (ite p (A (int 1)) (B y)), p]).forget [⟨"p", ()⟩]) (isA s1)
#guard closes env ((factsOf [eq s1 (A y)]).forget [⟨"p", ()⟩]) (isA s1)
#guard !closes env ((factsOf [imp p (g y)]).forget [⟨"y", ()⟩]) (imp p (g y))
#guard closes env ((factsOf [p, not p]).forget [⟨"p", ()⟩]) (g y)

-- `assume` records a definition as written, and its rewritten form.
#guard ((factsOf [eq s1 (ite p (A (int 1)) (B y))]).defs.get? ⟨"s1", ()⟩).map (·.written)
  == some (ite p (A (int 1)) (B y))
#guard ((factsOf [p, eq s1 (ite p (A (int 1)) (B y))]).defs.get? ⟨"s1", ()⟩).map (·.simplified)
  == some (A (int 1))
-- A value or constructor application is a value, not a definition.
#guard !(factsOf [eq s1 (A (int 1))]).defs.contains ⟨"s1", ()⟩
#guard provedFrom [eq s1 (A (int 1))] (isA s1)
-- An equation between two variables defines the left one by the right one, so facts about one
-- apply to the other where a rule reads through the definition.
private def x1 := var "x1" tT
private def x2 := var "x2" tT
#guard ((factsOf [eq x1 x2]).defs.get? ⟨"x1", ()⟩).map (·.written) == some x2
#guard !(factsOf [eq x1 x2]).defs.contains ⟨"x2", ()⟩
#guard provedFrom [isA x2, eq x1 x2] (isA x1)
#guard provedFrom [eq x1 x2, isA x2] (isA x1)
#guard !provedFrom [eq x1 x2, isA x1] (isA x2)
-- When the left one has a definition, the right one is defined by it.
#guard ((factsOf [eq x1 (ite p x (A y)), eq x1 x2]).defs.get? ⟨"x2", ()⟩).map (·.written)
  == some x1
#guard provedFrom [eq x1 (ite p x (A y)), eq x1 x2, isA x] (isA x2)
-- No cycle of definitions.
#guard !(factsOf [eq x1 x2, eq x2 x1]).defs.contains ⟨"x2", ()⟩

/-! ## Backchaining

A rule's hypotheses are discharged by rewriting them under the same context. -/

-- A hypothesis that needs a fact: the keys are different by the fact.
#guard provedFrom [not (eq i j)] (eq (sel "" (upd "" mk i v) j) (sel "" mk j))
-- A hypothesis that cannot be discharged: nothing says whether the keys are equal.
#guard !proved (eq (sel "" (upd "" mk i v) j) (sel "" mk j))
-- A hypothesis that needs a rule: the keys differ by their constructors.
#guard proved (eq (selT (updT mt (A y) v) C) (selT mt C))

/-- A rule over no theory: `g(k) → true if g(k + 1)` for an integer literal `k`. -/
private def stepRule : CondRule Unit where
  name := "step"
  heads _ h := match h with | .op n => n == "g" | _ => false
  apply _ e := match e with
    | .app _ fn (.const _ (.intConst k)) =>
      some (tt, [.app m fn (.intConst m (k + 1))])
    | _ => none

/-- An environment with only `stepRule`. -/
private def stepEnv : Env Unit :=
  Env.build factory (Theories.ofFactory factory []).bool.connectives () [stepRule] true

/-- Whether `g(k)` is proved from the fact `g(5)` with `stepRule`. -/
private def stepProved (k : Int) : Bool :=
  closes stepEnv (Facts.assume stepEnv Facts.empty (g (int 5))) (g (int k))

-- `g(1)` needs four applications in a row; the last hypothesis, `g(5)`, holds by the fact
-- directly. `g(0)` needs one more than the backchaining depth allows.
#guard maxBackchain = 3
#guard stepProved 5 && stepProved 4 && stepProved 1
#guard !stepProved 0

/-! ## The size bound

A goal or assumption whose tree has more than `maxTreeSize` nodes is left alone. -/

/-- `y + y` doubled `k` times, sharing its halves: a tree of `2^(k+3) - 3` nodes. -/
private def doubled : Nat → Expression.Expr
  | 0 => add y y
  | k + 1 => let d := doubled k; add d d

#guard !tooLarge (doubled 13) && tooLarge (doubled 14)
#guard closes env Facts.empty (le (doubled 12) (doubled 12))
#guard (rewrite env Facts.empty (le (doubled 13) (doubled 13))).2.tooLarge
#guard !closes env Facts.empty (le (doubled 13) (doubled 13))
-- An assumption larger than the bound gives no fact and cannot end the path.
#guard closes env (factsOf [and p (le (doubled 12) y)]) p
#guard !closes env (factsOf [and p (le (doubled 14) y)]) p
#guard !(factsOf [and (not p) (and p (le (doubled 14) y))]).isDead

/-! ## The definition allowance

Reading through a definition charges its expanded tree size against an allowance of
`maxTreeSize` nodes per goal; a definition larger than what is left is not read. -/

/-- `t0 := ite p₀ (A y) (A z)` and `tₖ₊₁ := ite pₖ₊₁ tₖ tₖ`: the expanded tree of `tₖ`
    about doubles with each `k`. -/
private def tv (k : Nat) : Expression.Expr := var s!"t{k}" tT
private def chain (k : Nat) : List Expression.Expr :=
  eq (tv 0) (ite (var "p0" .bool) (A y) (A z)) ::
    (List.range k).map fun i => eq (tv (i + 1)) (ite (var s!"p{i+1}" .bool) (tv i) (tv i))

#guard provedFrom (chain 3) (isA (tv 3))
-- The expanded size of `tₖ` is `10 * 2^k - 2`. Proving `isA(tₖ)` reads `tₖ`, …, `t₀`.
#guard ((factsOf (chain 12)).defs.get? ⟨"t12", ()⟩).map (·.expandedSize) == some 40958
#guard provedFrom (chain 12) (isA (tv 12))
#guard !provedFrom (chain 13) (isA (tv 13))
-- The expanded size saturates above `maxTreeSize`.
#guard ((factsOf (chain 14)).defs.get? ⟨"t14", ()⟩).map (·.expandedSize) == some 100001

end Core.ContextualRewrite.Tests

end
