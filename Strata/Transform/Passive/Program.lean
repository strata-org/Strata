/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.CmdProps
public import Std.Data.HashSet
public import Std.Data.HashMap
import Strata.Util.ExceptProps

/-! # Vocabulary of the WP and SSA phases (language-generic)

The WP phase (`WP/WP.lean`) turns a *loop-free program* (structured, without loops or calls, with
deterministic guards) into a *guarded program*, and the SSA phase (`SSA/SSA.lean`) turns a guarded
program into an *obligation program* (`init`/`assume`/`assert`/`cover` commands combined by
nondeterministic `ite`s, as consumed by obligation extraction), generic over the expression
language `P` (see `WPOps`, `WPLang`).  This file holds what both phases, their composition and their
correctness statements share:

* renamings (`Ren`) and source-variable types (`Tys`);
* reachability conditions (`RE`): `top`, a Boolean name, the negation of a guard name, or the
  conjunction of a Boolean name with the negation of a guard name;
* the flat output (`Item`: straight-line statements, side branches of obligations under one
  reachability, real branches) and its nesting into a statement list (`nest`, computed in one
  pass by `nestFast`);
* the *choice record* of the SSA phase (`LogEntry`, `substObl`): the substitution under which
  each loop-free obligation is emitted;
* fresh names `b@n` (`freshName`) outside a two-level hash set of avoided names (`AvoidSet`,
  `freshIn`); `baseOf` strips the counter of a fresh name; the initial state of both phases
  (`FreshSt`: counter, avoided names, free-variable types) and the names a phase avoids for its
  input (`inputAvoid`).

Key definitions: `RE`, `Item`, `nest`, `LogEntry`, `substObl`, `freshName`, `AvoidSet`,
`freshIn`, `FreshSt`, `inputAvoid`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPOps P]

/-! ## Names, renamings, expressions -/


/-- A renaming: source variable → current SSA name (first binding wins; unbound
    variables are their own current name). -/
abbrev Ren (P : PureExpr) := List (P.Ident × P.Ident)

/-- The current name of `x` under `ρ`. -/
@[expose] def Ren.get (ρ : (Ren P)) (x : P.Ident) : P.Ident :=
  match ρ.find? (fun p => p.1 == x) with
  | some p => p.2
  | none => x

/-- Rename `x` to `y`, shadowing earlier bindings of `x`. -/
@[expose] def Ren.set (ρ : (Ren P)) (x y : P.Ident) : (Ren P) := (x, y) :: ρ

/-- Source-variable types. -/
abbrev Tys (P : PureExpr) := List (P.Ident × P.Ty)

/-- The type recorded for `x`, if any (first binding wins). -/
@[expose] def Tys.get? (tys : (Tys P)) (x : P.Ident) : Option P.Ty :=
  (tys.find? (fun p => p.1 == x)).map (·.2)

/-! ## Reachability conditions and the flat output -/

/-- A reachability condition: `top` (reached whenever the enclosing path is), a Boolean
    name, the negation `¬g` of a guard name, or `q ∧ ¬g` for a Boolean name `q` and a guard
    name `g`.  Literals and negations are kept inline. -/
inductive RE (P : PureExpr) where
  | top
  | name (r : P.Ident)
  | neg (g : P.Ident)
  | andNeg (q g : P.Ident)
  deriving Inhabited

instance : DecidableEq (RE P) := fun a b =>
  match a, b with
  | .top, .top => isTrue rfl
  | .name r, .name r' =>
    if h : r = r' then isTrue (h ▸ rfl) else isFalse (fun e => h (RE.name.inj e))
  | .neg g, .neg g' =>
    if h : g = g' then isTrue (h ▸ rfl) else isFalse (fun e => h (RE.neg.inj e))
  | .andNeg q g, .andNeg q' g' =>
    if h : q = q' ∧ g = g' then isTrue (h.1 ▸ h.2 ▸ rfl)
    else isFalse (fun e => h ⟨(RE.andNeg.inj e).1, (RE.andNeg.inj e).2⟩)
  | .top, .name _ | .top, .neg _ | .top, .andNeg _ _ | .name _, .top | .name _, .neg _
  | .name _, .andNeg _ _ | .neg _, .top | .neg _, .name _ | .neg _, .andNeg _ _
  | .andNeg _ _, .top | .andNeg _ _, .name _ | .andNeg _ _, .neg _ =>
    isFalse (fun e => by cases e)

/-- The Boolean expression of a reachability condition. -/
@[expose] def RE.expr : (RE P) → P.Expr
  | .top => tt
  | .name r => HasFvar.mkBoolVar r
  | .neg g => notE (HasFvar.mkBoolVar g)
  | .andNeg q g => andE (HasFvar.mkBoolVar q) (notE (HasFvar.mkBoolVar g))

/-- `ite(r, t, e)` with the condition folded: `t` for `top`, `ite(g, e, t)` for `¬g`,
    `ite(q, ite(g, e, t), e)` for `q ∧ ¬g`. -/
@[expose] def RE.ite (r : RE P) (t e : P.Expr) : P.Expr :=
  match r with
  | .top => t
  | .name r => WPOps.ite (HasFvar.mkBoolVar r) t e
  | .neg g => WPOps.ite (HasFvar.mkBoolVar g) e t
  | .andNeg q g => WPOps.ite (HasFvar.mkBoolVar q) (WPOps.ite (HasFvar.mkBoolVar g) e t) e

/-- The label of generated reachability assumptions. -/
@[expose] def reachLabel : String := "wp$reach"

/-- The reachability assumption opening a side branch: none when always reached. -/
@[expose] def reachPre : Option (RE P) → (PStmts P)
  | none | some .top => []
  | some r => [.cmd (.cmd (.assume reachLabel r.expr .empty))]

/-- One element of the flat translation. -/
inductive Item (P : PureExpr) where
  /-- A straight-line statement of the obligation program. -/
  | plain (s : (PStmt P))
  /-- A side branch: the consecutive obligations `cs` under the reachability `reach`. -/
  | obls (reach : Option (RE P)) (cs : (PStmts P))
  /-- A real branch: the flat translations `t` and `e` of the two arms of an `ite` after which
      no obligation follows.  It ends the main path. -/
  | branch (t e : List (Item P))
  deriving Inhabited

/-- Does the item leave the main path (a side branch or a real branch)? -/
@[expose] def Item.isBranching : (Item P) → Bool
  | .plain _ => false
  | .obls _ _ | .branch _ _ => true

mutual
/-- Turn the flat translation into the obligation program. -/
@[expose] def nest : List (Item P) → (PStmts P)
  | [] => []
  | it :: rest => nestCons it rest (nest rest)

/-- `nest (it :: rest)`, given `nr = nest rest`: a straight-line statement is kept when a
    branching item follows; a side branch becomes the `then` branch of a nondeterministic `ite`
    whose `else` branch is `nr`, and is inline when no branching item follows; a real branch
    becomes a nondeterministic `ite` of its nested arms, or the one nested arm that is not
    empty, and ends the list. -/
@[expose] def nestCons : Item P → List (Item P) → (PStmts P) → (PStmts P)
  | .plain s, rest, nr => if rest.any Item.isBranching then s :: nr else []
  | .obls r cs, rest, nr =>
    let b := reachPre r ++ cs
    if rest.any Item.isBranching then [.ite .nondet b nr .empty] else b
  | .branch t e, _, _ =>
    match nest t, nest e with
    | [], e' => e'
    | t', [] => t'
    | t', e' => [.ite .nondet t' e' .empty]
end

mutual
/-- `nest` of an item list, with whether one of its items leaves the main path
    (`Item.isBranching`), in one pass over the list. -/
@[expose] def nestB : List (Item P) → (PStmts P) × Bool
  | [] => ([], false)
  | it :: rest =>
    let (nr, b) := nestB rest
    (nestConsB it b nr, it.isBranching || b)

/-- `nestCons it rest nr`, given `b`, whether an item of `rest` leaves the main path. -/
@[expose] def nestConsB : Item P → Bool → (PStmts P) → (PStmts P)
  | .plain s, b, nr => if b then s :: nr else []
  | .obls r cs, b, nr =>
    let bs := reachPre r ++ cs
    if b then [.ite .nondet bs nr .empty] else bs
  | .branch t e, _, _ =>
    match (nestB t).1, (nestB e).1 with
    | [], e' => e'
    | t', [] => t'
    | t', e' => [.ite .nondet t' e' .empty]
end

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasSubstFvar P] [HasIdent P]
    [Hashable P.Ident] [HasFvars P] in
mutual
/-- `nestB` computes `nest` and whether an item leaves the main path. -/
private theorem nestB_eq : ∀ l : List (Item P), nestB l = (nest l, l.any Item.isBranching)
  | [] => rfl
  | it :: rest => by
    rw [nestB, nestB_eq rest, nest, List.any_cons, ← nestConsB_eq it rest]
/-- `nestConsB` is `nestCons` given whether an item of the rest leaves the main path. -/
private theorem nestConsB_eq : ∀ (it : Item P) (rest : List (Item P)) (nr : PStmts P),
    nestConsB it (rest.any Item.isBranching) nr = nestCons it rest nr
  | .plain _, _, _ => rfl
  | .obls _ _, _, _ => rfl
  | .branch t e, _, _ => by rw [nestConsB, nestCons, nestB_eq t, nestB_eq e]
end

/-- `nest` computed in one pass over the list (`nestB`). -/
@[expose] def nestFast (l : List (Item P)) : PStmts P := (nestB l).1

/-- The compiled code of `nest` is `nestFast`, linear in the number of items where `nest`
    rescans the rest of the list at each item. -/
@[csimp] theorem nest_eq_nestFast : @nest = @nestFast := by
  funext
  simp only [nestFast, nestB_eq]


/-! ## The choice record -/

/-- An entry of the record of the obligations the SSA phase emits. -/
inductive LogEntry (P : PureExpr) where
  /-- An obligation with label `label`, emitted on the SSA names: `sub` maps each renamed
      free variable `x` of its loop-free condition to its current name `y` and the type
      annotation `ty` of the emitted variable, so the emitted condition is the loop-free one
      with each such `x` replaced by `y : ty` (`substObl`), and the loop-free condition is the
      emitted one with `sub` inverted. -/
  | obl (label : String) (sub : List (P.Ident × P.Ident × Option P.Ty))
  deriving Inhabited

/-- The condition an obligation of the obligation program has, for the loop-free condition `e`
    and the substitution `sub` of its choice-record entry: each `x` with `(x, y, ty)` in `sub`
    replaced by the variable `y` annotated `ty`. -/
@[expose] def substObl (sub : List (P.Ident × P.Ident × Option P.Ty)) (e : P.Expr) : P.Expr :=
  HasSubstFvar.substFvars e (sub.map fun (x, y, ty) => (x, HasFvar.mkVar y ty))

/-! ## Fresh names -/

/-- The name the pass introduces with base `b` and counter `n`: `b@n`. -/
@[expose] def freshName (b : String) (n : Nat) : P.Ident :=
  HasIdent.ident (P := P) (b ++ "@" ++ toString n)

/-- The label of generated join assumptions. -/
@[expose] def joinLabel : String := "wp$join"

/-- The statement `init x : ty := e`. -/
@[expose] def mkInit (x : P.Ident) (ty : P.Ty) (e : ExprOrNondet P) :
    (PStmt P) := .cmd (.cmd (.init x ty e .empty))
/-- The statement `assume l : e`. -/
@[expose] def mkAssume (l : String) (e : P.Expr) : (PStmt P) :=
  .cmd (.cmd (.assume l e .empty))


/-- A hash set of identifiers. -/
abbrev IdSet (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] :=
  Std.HashSet P.Ident

/-- The hash set of the identifiers of a list. -/
@[expose] def IdSet.ofList (l : List P.Ident) : IdSet P := Std.HashSet.ofList l

/-- The names fresh names avoid, in two levels: the global names `glob` (built once per program
    and shared by its procedures) and the identifiers `loc` of one procedure. -/
structure AvoidSet (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] where
  glob : IdSet P
  loc : IdSet P

/-- Is `x` avoided? -/
@[expose] def AvoidSet.contains (a : AvoidSet P) (x : P.Ident) : Bool :=
  a.glob.contains x || a.loc.contains x

/-- The avoided names, as a list. -/
@[expose] def AvoidSet.toList (a : AvoidSet P) : List P.Ident := a.glob.toList ++ a.loc.toList

/-- The first counter from `n` (within `fuel` tries) whose name with base `b` is not avoided. -/
@[expose] def freeCounterIn (avoid : AvoidSet P) (b : String) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n =>
    if avoid.contains (freshName b n) then freeCounterIn avoid b fuel (n + 1) else n

/-- A fresh name with base `b` from counter `n`: `freshName b k` for the least `k ≥ n` whose
    name is not avoided, and the counter advanced past it. -/
@[expose] def freshIn (avoid : AvoidSet P) (b : String) (n : Nat) : P.Ident × Nat :=
  let k := freeCounterIn avoid b (avoid.glob.size + avoid.loc.size + 1) n
  (freshName b k, k + 1)

/-- The base of a name: the name without one trailing `@digits` (the counter of a fresh name). -/
@[expose] def baseOf (x : P.Ident) : String :=
  let cs := (WPOps.name x).toList.reverse
  let digits := cs.takeWhile Char.isDigit
  match cs.drop digits.length with
  | '@' :: pre => if digits.isEmpty then WPOps.name x else String.ofList pre.reverse
  | _ => WPOps.name x

/-- The initial state of the WP and SSA phases: fresh-name counter, avoided names, types of the
    free variables. -/
structure FreshSt (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] where
  next : Nat
  avoid : AvoidSet P
  tys : Tys P

/-- The names a phase avoids for its input `ss` with free-variable types `tys`: the names of `G`
    (the names of the enclosing program), the identifiers of `ss` and the free variables. -/
@[expose] def inputAvoid (G : IdSet P) (tys : Tys P) (ss : PStmts P) : AvoidSet P :=
  ⟨G, IdSet.ofList (Block.idents ss ++ tys.map (·.1))⟩

end -- public section

end WP
end Imperative
