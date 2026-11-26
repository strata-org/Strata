/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.PassiveVCGen

meta section

/-! # Differential tests: weakest-precondition vs strongest-postcondition VCs

Grigore et al., "Strongest Postcondition of Unstructured Programs" (FTfJP 2009),
prove that the WP and SP methods yield VCs that are equivalent but structurally
different (their §4, Example 2). This file checks both halves of that claim on
concrete passive CFGs:

* equivalent: `vc .wp p` and `vc .sp p` are logically equivalent, verified by
  evaluating both formulas under every Boolean assignment to their free
  variables (a truth table, so no SMT solver is needed);
* structurally different: the two VCs are not syntactically identical.

To keep the check decidable and solver-free, we instantiate the passification
`PureExpr` interface with a small Boolean expression language `BExpr` whose
evaluator is an ordinary truth-table function. `Cmd.assume`/`assert`'s guard,
the incarnation equalities `x@i == e` (modelled as Boolean bi-implication), and
the WP/SP connectives all live in this language. -/

namespace Imperative.PassiveVCGen.DiffTest
open Imperative
open Imperative.PassiveVCGen

/-! ## A minimal Boolean `PureExpr` with a real evaluator -/

inductive BExpr where
  | tt
  | ff
  | var (x : String)
  | not (e : BExpr)
  | and (a b : BExpr)
  | or  (a b : BExpr)
  | imp (a b : BExpr)
  /-- Boolean "equality" (bi-implication). Passification emits `x@i == e`; over
      Boolean variables the natural interpretation of `==` is `iff`. -/
  | beq (a b : BExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Free variables of a `BExpr`. -/
def BExpr.vars : BExpr → List String
  | .tt | .ff => []
  | .var x    => [x]
  | .not e    => e.vars
  | .and a b | .or a b | .imp a b | .beq a b => a.vars ++ b.vars

/-- Truth-table evaluation under a Boolean assignment `ρ`. -/
def BExpr.eval (ρ : String → Bool) : BExpr → Bool
  | .tt      => true
  | .ff      => false
  | .var x   => ρ x
  | .not e   => !(e.eval ρ)
  | .and a b => a.eval ρ && b.eval ρ
  | .or  a b => a.eval ρ || b.eval ρ
  | .imp a b => !(a.eval ρ) || b.eval ρ
  | .beq a b => a.eval ρ == b.eval ρ

/-- Capture-avoiding simultaneous substitution of variables by `BExpr`s. -/
def BExpr.subst (m : List (String × BExpr)) : BExpr → BExpr
  | .tt      => .tt
  | .ff      => .ff
  | .var x   => match m.find? (fun p => p.1 == x) with
                | some p => p.2
                | none   => .var x
  | .not e   => .not (e.subst m)
  | .and a b => .and (a.subst m) (b.subst m)
  | .or  a b => .or  (a.subst m) (b.subst m)
  | .imp a b => .imp (a.subst m) (b.subst m)
  | .beq a b => .beq (a.subst m) (b.subst m)

abbrev BPure : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := BExpr,
    -- Values are the closed expressions the truth-table evaluator returns.
    Val := BExpr,
    Ty := Unit,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    Factory := Unit,
    eval := fun _f _σ e => some e }

instance : HasVal BPure where
  value _ _ := True
  valueOfTy _ _ _ := True

instance : HasBool BPure where
  tt := .tt
  ff := .ff
  tt_is_not_ff := by intro h; cases h
  boolTy := ()
  ttVal := fun _ => .tt
  ffVal := fun _ => .ff
  ttVal_ne_ffVal := fun _ h => by cases h
  boolIsValOfTy := fun _ => ⟨trivial, trivial⟩

instance : HasBoolOps BPure where
  not := .not
  and := .and
  or  := .or
  imp := .imp

instance : HasFvar BPure where
  mkFvar x := .var x
  mkTypedFvar x _ := .var x
  getFvar := fun | .var x => some x | _ => none

instance : HasFvars BPure where
  getFvars := BExpr.vars
  -- `BExpr` variables carry no type annotations.
  getTypedFvars := fun _ => []

instance : HasIdent BPure where
  ident s := s

instance : HasSubstFvar BPure where
  substFvar e x r := BExpr.subst [(x, r)] e
  substFvars e m := BExpr.subst m e
  -- `BExpr` variables are untyped, so renaming is substitution by bare vars.
  renameFvars e m := BExpr.subst (m.map fun (a, b) => (a, .var b)) e

instance : HasInt BPure where
  zero := .ff
  intTy := ()
  -- `zero` (`.ff`) must be a numeral; that is all `HasInt` requires here.
  isNumeral := fun e => match e with | .ff => true | _ => false
  isNumeralVal := fun v => match v with | .ff => true | _ => false
  zeroIsNumeral := rfl
  numeralHasNoFvars := fun n h => by
    cases n <;> simp only [] at h ⊢ <;> first | rfl | contradiction

/-- Integer "equality" is Boolean bi-implication in this test language, so the
    incarnation constraints `x@i == e` that passification emits are ordinary
    `BExpr`s the truth-table evaluator understands. -/
instance : HasIntOps BPure where
  eq a b := .beq a b
  lt a b := .imp a b

/-! ## Deciding logical equivalence by truth table -/

/-- All Boolean assignments to `vars`, as association lists. -/
def allAssignments : List String → List (List (String × Bool))
  | []      => [[]]
  | x :: xs =>
    let rest := allAssignments xs
    rest.map (fun ρ => (x, false) :: ρ) ++ rest.map (fun ρ => (x, true) :: ρ)

/-- Look a variable up in an assignment (absent ⇒ `false`). -/
def lookup (ρ : List (String × Bool)) (x : String) : Bool :=
  (ρ.find? (fun p => p.1 == x)).map (·.2) |>.getD false

/-- Are two `BExpr`s logically equivalent? Checked exhaustively over every
    assignment to the union of their free variables. -/
def equiv (e1 e2 : BExpr) : Bool :=
  let vars := (e1.vars ++ e2.vars).eraseDups
  (allAssignments vars).all (fun ρ =>
    e1.eval (lookup ρ) == e2.eval (lookup ρ))

/-! ## CFG builders (metadata-free convenience) -/

/-- A block with body `cmds` transferring (non-deterministically) to `succs`. -/
def blk (cmds : List (Cmd BPure)) (succs : List String) : PBlock BPure :=
  mkBlock cmds succs

/-- `assume` / `assert` with an empty label and empty metadata. -/
def bassume (e : BExpr) : Cmd BPure := .assume "" e .empty
def bassert (e : BExpr) : Cmd BPure := .assert "" e .empty

/-! ## Test programs

These are already-passive CFGs (each variable written at most once per path),
so `passify` leaves their logical content intact and only re-runs incarnation
bookkeeping. That keeps the WP/SP comparison focused on VC generation. -/

/-- Straight line: `assume a; assert b`. -/
def progLine : PCFG BPure :=
  { entry := "n0",
    blocks := [("n0", blk [bassume (.var "a"), bassert (.var "b")] [])] }

/-- A diamond (join): entry branches to two assume-blocks that both reach an
    asserting join, the shape of the paper's Fig. 2 and 4. -/
def progDiamond : PCFG BPure :=
  { entry := "a",
    blocks :=
      [ ("a", blk [] ["b", "c"]),
        ("b", blk [bassume (.var "p")] ["d"]),
        ("c", blk [bassume (.not (.var "p"))] ["d"]),
        ("d", blk [bassert (.var "q")] []) ] }

/-- Two assertions on different paths, with an assumption feeding each. -/
def progTwoAsserts : PCFG BPure :=
  { entry := "s",
    blocks :=
      [ ("s", blk [bassume (.var "g")] ["t", "u"]),
        ("t", blk [bassert (.imp (.var "g") (.var "x"))] []),
        ("u", blk [bassume (.var "h"), bassert (.var "x")] []) ] }

/-- A block with an incarnation-style equality assumption, exercising the
    `HasIntOps.eq` (`==`) path that passification emits for assignments. -/
def progEq : PCFG BPure :=
  { entry := "m0",
    blocks :=
      [ ("m0", blk [bassume (.beq (.var "x1") (.var "x0"))] ["m1"]),
        ("m1", blk [bassert (.imp (.var "x0") (.var "x1"))] []) ] }

/-! ## Differential checks

For each program: (1) the WP VC and the SP VC are logically equivalent, and
(2) they are not syntactically identical (paper Example 2). -/


/-- `vc`, on a program it accepts (all the programs here are acyclic, with unique
    labels); `false` otherwise, which no check below expects. -/
def vcOk (m : VcMethod) (p : PCFG BPure) : BExpr := (vc m p).toOption.getD .ff

/-- info: true -/
#guard_msgs in #eval equiv (vcOk .wp progLine) (vcOk .sp progLine)

/-- info: true -/
#guard_msgs in #eval equiv (vcOk .wp progDiamond) (vcOk .sp progDiamond)

/-- info: true -/
#guard_msgs in #eval equiv (vcOk .wp progTwoAsserts) (vcOk .sp progTwoAsserts)

/-- info: true -/
#guard_msgs in #eval equiv (vcOk .wp progEq) (vcOk .sp progEq)

-- Equivalent but structurally different: the two VCs are not the same syntax
-- tree. (`progLine` alone can coincide for a single straight-line assertion, so
-- we assert distinctness on the branching programs, where the methods diverge.)
/-- info: true -/
#guard_msgs in #eval (vcOk .wp progDiamond ≠ vcOk .sp progDiamond : Bool)

/-- info: true -/
#guard_msgs in #eval (vcOk .wp progTwoAsserts ≠ vcOk .sp progTwoAsserts : Bool)

-- Sanity: a failing assertion is not made valid by either method.
-- `assert b` with `b` free is satisfiable-but-not-valid, so the WP VC (which is
-- `α₀`, here containing `b` as a conjunct/consequent) is not a tautology.
/-- info: false -/
#guard_msgs in #eval equiv (vcOk .wp progLine) .tt

/-! ## Critical edges

In `crit`, `B → J` is a critical edge: `B` has two successors and `J` two
predecessors. The incarnation of `x` that reaches `J` differs between `B` and
`C`, and the equality reconciling them must hold on the edge `B → J` only, not
in `B`, where it would also constrain the path through `C`. Passification splits
the edge with a fresh block for it. -/

def setc (x : String) (e : BExpr) : Cmd BPure := .set x (.det e) .empty

/-- `B: y := x; goto C, J`, `C: x := true; goto J`, `J: assert [l] goal`. -/
def crit (goal : BExpr) : PCFG BPure :=
  { entry := "B",
    blocks := [ ("B", blk [setc "y" (.var "x")] ["C", "J"]),
                ("C", blk [setc "x" .tt] ["J"]),
                ("J", blk [.assert "l" goal .empty] []) ] }

/-- Each assertion's label and whether its obligation is valid, with the VC's
    definitions inlined. -/
def checkAsserts (m : VcMethod) (p : PCFG BPure)
    (inline : Unit → Bool := fun _ => false) (declaredBeforeUse : Bool := false) :
    List (String × Bool) :=
  match defObligations m p (inline := inline) (declaredBeforeUse := declaredBeforeUse) with
  | .error _ => []
  | .ok v =>
    let inline := fun (env : List (String × BExpr)) (ds : List (String × BExpr)) =>
      ds.foldl (fun env (n, e) => (n, e.subst env) :: env) env
    let env := inline [] v.defs
    v.obligations.filterMap fun o =>
      if o.isCover then none
      else
        let env := inline env o.goalDefs
        some (o.label, equiv ((BExpr.imp (.and o.facts o.pre) o.goal).subst env) .tt)

/-- info: ["B", "$edge$B$J", "C", "J"] -/
#guard_msgs in #eval ((passify (crit .tt)).toOption.map (·.blocks.map (·.1))).getD []

-- `x ∨ x == y` holds at `J` on both paths: `x` is `true` through `C`, and `x`
-- equals `y` on the edge from `B`.
/-- info: ([("l", true)], [("l", true)]) -/
#guard_msgs in
#eval let g := BExpr.or (.var "x") (.beq (.var "x") (.var "y"))
      (checkAsserts .sp (crit g), checkAsserts .wp (crit g))

-- `x == y` fails through `C` when `x` is initially `false`.
/-- info: ([("l", false)], [("l", false)]) -/
#guard_msgs in
#eval let g := BExpr.beq (.var "x") (.var "y")
      (checkAsserts .sp (crit g), checkAsserts .wp (crit g))

/-! ## `passify` itself rejects a cycle

Passification needs a topological order, so `passify` (and `vc`) fail on a cycle
rather than give a wrong result. -/

/-- info: the control-flow graph has a cycle reachable from the entry, through [L]; cut its loops first (CFG loop elimination) -/
#guard_msgs in
#eval match passify ({ entry := "A", blocks := [("A", blk [] ["L"]),
    ("L", blk [bassert .tt] ["L", "B"]), ("B", blk [] [])] } : PCFG BPure) with
  | .error e => IO.println e
  | .ok _ => IO.println "accepted"

/-! ## Repeated labels are rejected -/

/-- info: the control-flow graph has two blocks labelled 'B' -/
#guard_msgs in
#eval match defObligations .sp
    ({ entry := "A", blocks := [("A", blk [] ["B"]), ("B", blk [bassert .tt] []),
                                ("B", blk [bassert .ff] [])] } : PCFG BPure) with
  | .error e => IO.println e
  | .ok _ => IO.println "accepted"

/-! ## A long chain of joins

A chain of `n` diamonds, each writing a fresh variable on one arm, goes through
passification and VC generation in one piece. (Reconciling every variable at
every join, rather than only those written since its immediate dominator, would
give the same output here, as the other variables agree on both predecessors;
these checks do not tell the two apart.) -/

/-- `n` diamonds; diamond `i` writes `x_i` on its left arm, and the last block
    asserts `x0 == x0`. -/
def diamonds (n : Nat) : PCFG BPure :=
  let ds := (List.range n).flatMap fun i =>
    [ (s!"d{i}", blk [] [s!"l{i}", s!"r{i}"]),
      (s!"l{i}", blk [setc s!"x{i}" .tt] [s!"d{i+1}"]),
      (s!"r{i}", blk [] [s!"d{i+1}"]) ]
  { entry := "d0", blocks := ds ++ [(s!"d{n}", blk [bassert (.beq (.var "x0") (.var "x0"))] [])] }

/-- info: 1 -/
#guard_msgs in
#eval match defObligations .sp (diamonds 1000) with
  | .ok v => IO.println v.obligations.length
  | .error e => IO.println e

-- Under WP, only the blocks with an assertion get the weakest preconditions of
-- their ancestors: the one assertion here, in the last block, has one
-- definition per block, 3001 in all, and no other block has any.
/-- info: [3001] -/
#guard_msgs in
#eval match defObligations .wp (diamonds 1000) with
  | .ok v => IO.println (v.obligations.map fun (o : DefObligation BPure) => o.goalDefs.length)
  | .error e => IO.println e

-- Each assertion is checked on its own: `a1` does not assume `a0`, nor `a0` the
-- later `assume x`; only `a2`, after it, holds. Two blocks keep the WP chain
-- across an edge.
/-- info: ([("a0", false), ("a1", false), ("a2", true)], [("a0", false), ("a1", false), ("a2", true)]) -/
#guard_msgs in
#eval
  let p : PCFG BPure := { entry := "c0", blocks := [
    ("c0", blk [.assert "a0" (.var "x") .empty] ["c1"]),
    ("c1", blk [.assert "a1" (.var "x") .empty, .assume "" (.var "x") .empty,
                .assert "a2" (.var "x") .empty] []) ] }
  (checkAsserts .wp p, checkAsserts .sp p)

/-! ## Inlined writes at a join

A write to a variable of an inlined type (here every variable: the type `Unit` is
the only one) emits no equality: its incarnation is defined as the value. At a join
of paths that differ in it, the variable is unconstrained, whichever predecessor
comes first in the block list. `assume x` on one path does not make `assert x` hold
after the join. -/

/-- `b0: init x; assume x` goes to `b1: x := L1` and `b2` (empty); `b3: assert x`. -/
def inlineJoin (b1First : Bool) : PCFG BPure :=
  let b1 := ("b1", blk [setc "x" (.var "L1")] ["b3"])
  let b2 := ("b2", blk [] ["b3"])
  { entry := "b0",
    blocks := [("b0", blk [.init "x" () .nondet .empty, bassume (.var "x")] ["b1", "b2"])] ++
      (if b1First then [b1, b2] else [b2, b1]) ++ [("b3", blk [bassert (.var "x")] [])] }

/-- info: ([("", false)], [("", false)], [("", false)], [("", false)]) -/
#guard_msgs in
#eval
  let inl := fun (_ : Unit) => true
  (checkAsserts .sp (inlineJoin true) inl, checkAsserts .wp (inlineJoin true) inl,
   checkAsserts .sp (inlineJoin false) inl, checkAsserts .wp (inlineJoin false) inl)

/-- As `inlineJoin`, with no declaration of `x`: `b2` leaves it at its value on entry. -/
def inlineJoinUndeclared : PCFG BPure :=
  { entry := "b0",
    blocks := [("b0", blk [] ["b1", "b2"]), ("b1", blk [setc "x" .tt] ["b3"]),
               ("b2", blk [] ["b3"]), ("b3", blk [bassert (.var "x")] [])] }

-- `x` is written `true` on one path and not at all on the other, where it is its value on
-- entry, so `assert x` fails. A join treats a variable missing from a predecessor as
-- declared on the other paths only, needing no reset, only when told the language declares
-- every variable before reading it; here, where `x` is read undeclared, it may not be told.
/-- info: ([("", false)], [("", false)]) -/
#guard_msgs in
#eval
  let inl := fun (_ : Unit) => true
  (checkAsserts .sp inlineJoinUndeclared inl, checkAsserts .wp inlineJoinUndeclared inl)

end Imperative.PassiveVCGen.DiffTest
