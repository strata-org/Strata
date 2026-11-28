/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core

/-! # Random Core programs for differential tests

`generate seed` is a random `Core.Program`, the same for the same seed: one to three
procedures over `int` and `bool` parameters, whose bodies are structured, loop-free and
call-free. The bodies declare variables (with and without an initial value), assign and
havoc them, assert and assume Boolean expressions, branch (on a Boolean expression, on a
constant guard, or nondeterministically), and open labeled blocks that `exit` leaves early.
Every expression is well-typed in the scope where it occurs, and every assertion has a
label of its own (`a0`, `a1`, …), so verdicts and concrete failures can be matched by label.

Among the programs are the shapes of three soundness bugs fixed in Core's verifier: an `if`
whose guard folds to a constant and whose live arm declares a name declared again after it
(`f5540d7d`), variables declared without a value and read after later writes (`02e45d94`),
and an `assume` followed by an `exit` out of a block, in a procedure before another one
(`3a949942`). Local names come from a pool of four, so that sibling scopes reuse them.

The programs are built as the DDM translation builds them: variables and operators carry
their types, and a negative literal is `Int.Neg` of a natural number. Every expression has
the synthesized source location `loc`, and statements have empty metadata. So
`Core.formatProgram` prints them in Core syntax, and the parser gives the same program back,
up to locations and metadata. -/

meta section
public section

namespace Core.RandomPrograms

open Lambda (LMonoTy)

/-! ## Random choices

A generator is a function of a random-number generator, threaded through `GenM` with the
counters that keep labels unique in a program. -/

/-- The generator's state: the random-number generator, and the number of assertions,
    assumptions and blocks generated so far, which name the next ones. -/
structure GenState where
  rng : StdGen
  asserts : Nat := 0
  assumes : Nat := 0
  blocks : Nat := 0

/-- Generators. -/
abbrev GenM := StateM GenState

/-- The state a generator of seed `seed` starts from. Its first number is dropped: for every
    seed below 53,667 it is `40014 * (seed + 1) - 40692` modulo `2147483562`, a multiple of 3,
    so `below 3` would always give `2`. The numbers are Lean's `StdGen`; a test pins a seed. -/
def GenState.ofSeed (seed : Nat) : GenState := { rng := (stdNext (mkStdGen seed)).2 }

/-- A number below `n`, uniformly; `0` when `n = 0`. -/
def below (n : Nat) : GenM Nat := modifyGet fun s =>
  let (k, rng) := randNat s.rng 0 (n - 1)
  (k, { s with rng })

/-- An element of `xs`, uniformly; `default` when `xs` is empty. -/
def pick {α : Type} [Inhabited α] (xs : List α) : GenM α := do
  return xs.getD (← below xs.length) default

/-- The result of one of `cases`, chosen with probability proportional to its weight. -/
def weighted {α : Type} [Inhabited α] (cases : List (Nat × GenM α)) : GenM α := do
  let mut k ← below (cases.foldl (· + ·.1) 0)
  for (w, g) in cases do
    if k < w then return ← g
    k := k - w
  return default

/-! ## Expressions -/

/-- What a statement may refer to: the variables in scope, innermost first, with their types
    and whether they are locals (only locals are assigned), and the labels of the enclosing
    blocks. -/
structure Scope where
  vars : List (String × LMonoTy × Bool) := []
  labels : List String := []
  deriving Inhabited

/-- The names of the variables of type `ty` in `s`. -/
def Scope.ofType (s : Scope) (ty : LMonoTy) : List String :=
  (s.vars.filter (·.2.1 == ty)).map (·.1)

/-- The source location of every expression the generator builds. -/
def loc : ExprSourceLoc := .synthesized "random-program"

/-- The variable `x` of type `ty`. -/
def var (x : String) (ty : LMonoTy) : Expression.Expr := .fvar loc ⟨x, ()⟩ (some ty)

/-- The operator `op` applied to `a` and `b`. -/
def app2 (op a b : Expression.Expr) : Expression.Expr := .app loc (.app loc op a) b

/-- The integer literal `n`; a negative one is `Int.Neg` of a natural number. -/
def intLit (n : Int) : Expression.Expr :=
  if n < 0 then .app loc intNegOp (.intConst loc (-n)) else .intConst loc n

/-- A small integer, between `-3` and `3`, or now and then `10` or `-10`. -/
def smallInt : GenM Int := do
  if (← below 8) == 0 then pick [10, -10] else return (← below 7 : Nat) - (3 : Int)

/-- A random value of type `ty` for an input: an integer drawn by `smallInt`, or either
    Boolean; `none` for any other type. Unlike `leaf`'s literals, a negative integer is one
    constant, not `Int.Neg` of a natural number. -/
def value (ty : LMonoTy) : Option (GenM Expression.Expr) :=
  if ty == .int then some do return .intConst valueLoc (← smallInt)
  else if ty == .bool then some do return .boolConst valueLoc ((← below 2) == 0)
  else none

/-- A variable of type `ty` in `s`, or a literal. -/
def leaf (s : Scope) (ty : LMonoTy) : GenM Expression.Expr := do
  let vs := s.ofType ty
  if vs.isEmpty || (← below 4) == 0 then
    if ty == .int then return intLit (← smallInt) else return .boolConst loc ((← below 2) == 0)
  else return var (← pick vs) ty

/-- An expression of type `ty` (`int` or `bool`) in `s`, at most `depth` operators deep.
    Divisors are nonzero literals, so that no division by zero needs a meaning. -/
def expr (s : Scope) (ty : LMonoTy) : Nat → GenM Expression.Expr
  | 0 => leaf s ty
  | d + 1 =>
    if ty == .int then weighted [
      (4, leaf s .int),
      (2, return app2 intAddOp (← expr s .int d) (← expr s .int d)),
      (2, return app2 intSubOp (← expr s .int d) (← expr s .int d)),
      (1, return app2 intMulOp (← expr s .int d) (intLit (← smallInt))),
      (1, return .app loc intNegOp (← expr s .int d)),
      (1, do
        let op ← pick [intDivOp, intModOp, intDivTOp, intModTOp]
        return app2 op (← expr s .int d) (intLit (← pick [2, 3, -2, -3]))),
      (1, return .ite loc (← expr s .bool d) (← expr s .int d) (← expr s .int d))]
    else weighted [
      (2, leaf s .bool),
      (4, do
        let op ← pick [intLtOp, intLeOp, intGtOp, intGeOp]
        return app2 op (← expr s .int d) (← expr s .int d)),
      (1, return .eq loc (← expr s .int d) (← expr s .int d)),
      (1, return .app loc boolNotOp (.eq loc (← expr s .int d) (← expr s .int d))),
      (1, return .app loc boolNotOp (← expr s .bool d)),
      (2, do
        let op ← pick [boolAndOp, boolOrOp, boolImpliesOp, boolEquivOp]
        return app2 op (← expr s .bool d) (← expr s .bool d)),
      (1, return .eq loc (← expr s .bool d) (← expr s .bool d)),
      (1, return .ite loc (← expr s .bool d) (← expr s .bool d) (← expr s .bool d))]

/-! ## Statements -/

/-- The pool of local names. It is small, so that sibling scopes declare the same names. -/
def localNames : List String := ["x", "y", "z", "w"]

/-- A guard of a branch: mostly a Boolean expression, sometimes one the evaluator folds
    (`true`, `false`, `v == v`), sometimes nondeterministic. -/
def branchGuard (s : Scope) : GenM (Imperative.ExprOrNondet Expression) := weighted [
  (5, return .det (← expr s .bool 2)),
  (1, return .det (.boolConst loc ((← below 2) == 0))),
  (1, do let v ← leaf s .int; return .det (.eq loc v v)),
  (1, return .nondet)]

/-- A fresh label: `a0`, `a1`, … for assertions, `assume_0`, `assume_1`, … for assumptions
    (the DDM translation's names for unlabeled ones), `L0`, `L1`, … for blocks. -/
def freshLabel (kind : String) : GenM String := do
  let st ← get
  match kind with
  | "assert" => set { st with asserts := st.asserts + 1 }; return s!"a{st.asserts}"
  | "assume" => set { st with assumes := st.assumes + 1 }; return s!"assume_{st.assumes}"
  | _ => set { st with blocks := st.blocks + 1 }; return s!"L{st.blocks}"

/-- A statement without nested statements, and the scope after it. -/
def simple (s : Scope) : GenM (Statement × Scope) := do
  let fresh := localNames.filter fun x => !(s.vars.any (·.1 == x))
  let locals := s.vars.filter (·.2.2)
  weighted [
    (if fresh.isEmpty then 0 else 3, do
      let x ← pick fresh
      let ty ← pick [LMonoTy.int, .int, .bool]
      let e ← if (← below 4) == 0 then pure .nondet else .det <$> expr s ty 2
      return (.init ⟨x, ()⟩ (.forAll [] ty) e #[], { s with vars := (x, ty, true) :: s.vars })),
    (if locals.isEmpty then 0 else 3, do
      let (x, ty, _) ← pick locals
      return (.set ⟨x, ()⟩ (← expr s ty 2) #[], s)),
    (if locals.isEmpty then 0 else 1, do
      return (.havoc ⟨(← pick locals).1, ()⟩ #[], s)),
    (3, do return (.assert (← freshLabel "assert") (← expr s .bool 2) #[], s)),
    (1, do
      let e ← if (← below 5) == 0 then pure (.boolConst loc false) else expr s .bool 2
      return (.assume (← freshLabel "assume") e #[], s))]

/-- `n` statements made by `step` in sequence, each in the scope the one before leaves. -/
def sequence (s : Scope) (n : Nat) (step : Scope → GenM (Statement × Scope)) :
    GenM (List Statement) := do
  let mut s := s
  let mut out := #[]
  for _ in [0:n] do
    let (st, s') ← step s
    out := out.push st
    s := s'
  return out.toList

/-- A list of statements in scope `s`, with branches and blocks nested at most `depth`
    deep. Declarations in a nested list are not in scope after it. -/
def stmts (s : Scope) : (depth : Nat) → GenM (List Statement)
  | 0 => do sequence s ((← below 3) + 1) simple
  | d + 1 => do
    sequence s ((← below 4) + 1) fun s => do
      let choice ← below 10
      if choice < 6 then simple s
      else if choice < 8 then
        let c ← branchGuard s
        let t ← stmts s d
        let f ← if (← below 3) == 0 then pure [] else stmts s d
        return (.ite c t f #[], s)
      else if choice < 9 || s.labels.isEmpty then
        let l ← freshLabel "block"
        return (.block l (← stmts { s with labels := l :: s.labels } d) #[], s)
      else return (.exit (← pick s.labels) #[], s)

/-! ## Procedures and programs -/

/-- A procedure named `name` with one to three parameters (`a`, `b`, `c`). -/
def proc (name : String) : GenM Procedure := do
  let params ← (["a", "b", "c"].take ((← below 3) + 1)).mapM fun x =>
    return (x, ← pick [LMonoTy.int, .int, .bool])
  let s : Scope := { vars := params.reverse.map fun (x, ty) => (x, ty, false) }
  return {
    header := { name := ⟨name, ()⟩, typeArgs := [], outputs := [],
                inputs := params.map fun (x, ty) => (⟨x, ()⟩, ty) }
    spec := { preconditions := [], postconditions := [] }
    body := .structured (← stmts s 3) false }

/-- The random program of seed `seed`: one to three procedures, `p0`, `p1`, …. -/
def generate (seed : Nat) : Program :=
  let gen : GenM Program := do
    let procs ← (List.range ((← below 3) + 1)).mapM fun i => proc s!"p{i}"
    return { decls := procs.map (.proc · #[]) }
  (gen.run (.ofSeed seed)).1

/-! ## Shrinking

A test that finds a program with a problem shrinks it greedily with `shrinks`, so that the
program it prints is small. A step may leave the program ill-formed (a read of a variable
whose declaration was removed, or a name declared twice after an arm is spliced into its
context); the shrinker keeps only candidates with a problem of the same kind. -/

mutual
/-- The statement lists that may replace `s` in a smaller program: an arm of a branch, the
    body of a block, or `s` with one of its own lists one step smaller. -/
def stmtShrinks : Statement → List (List Statement)
  | .ite c t f md => [t, f] ++ (stmtsShrinks t).map (fun t' => [.ite c t' f md])
      ++ (stmtsShrinks f).map (fun f' => [.ite c t f' md])
  | .block l b md => [b] ++ (stmtsShrinks b).map (fun b' => [.block l b' md])
  | _ => []

/-- The lists one step smaller than `ss`: one statement removed, or one statement replaced
    by one of its `stmtShrinks`. -/
def stmtsShrinks : List Statement → List (List Statement)
  | [] => []
  | s :: ss => [ss] ++ (stmtShrinks s).map (· ++ ss) ++ (stmtsShrinks ss).map (s :: ·)
end

/-- The programs one step smaller than `p`: one procedure removed, or one procedure's body
    one step smaller. -/
def shrinks (p : Program) : List Program :=
  let n := p.decls.length
  let dropOne := if n ≤ 1 then [] else (List.range n).map fun i => { decls := p.decls.eraseIdx i }
  let inBody := (List.range n).flatMap fun i => match p.decls[i]? with
    | some (Decl.proc q md) => match q.body with
      | .structured ss opq => (stmtsShrinks ss).map fun b =>
        { decls := p.decls.set i (.proc { q with body := .structured b opq } md) }
      | _ => []
    | _ => []
  dropOne ++ inBody

end Core.RandomPrograms

end -- public section
end -- meta section
