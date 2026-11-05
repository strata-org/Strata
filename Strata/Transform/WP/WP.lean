/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Program
public import Strata.Util.Rope
public import Strata.Util.LeftistHeap

/-! # The WP phase: loop-free program → guarded program (language-generic)

One backward traversal of a *loop-free program* (structured, without loops or calls, with
deterministic guards) producing a *guarded program*: an ordinary program in which every name is
declared by at most one `init`, whose statements are `init`, `set`, `assume`, `assert`, `cover`
and `ite *`, every `ite *` being the last statement of its list.  The SSA phase
(`SSA/SSA.lean`) turns it into an obligation program.

## Reach contexts

A list is emitted under a *reach context* `κ` (`RE`): `top` (the list is reached whenever the
path is) or a Boolean held in variables of the guarded program (`name r`, `neg g`, `andNeg q g`),
true exactly on the paths that reach the current point of the list.  Under a variable context,
assignments are *guarded*: `x := ite(κ, e, x)` leaves `x` unchanged off the paths that reach it
(*write-through*), assumptions become `κ ⟹ a`, and obligations are emitted in side branches
opened by `assume κ`.  After a statement that may exit, the context is updated (`setReach`): it
is false after the `exit` on the paths that took it.

## The traversal

`wpList κ d fEnd ss` processes the rest of a list before its head; `fEnd` says whether an
obligation follows the list (in an enclosing list), `d` is the number of enclosing blocks.  At
each statement, *an obligation follows* when the output emitted after it contains an `assert`
or a `cover`; statements after which none follows and that are not obligations are dropped.

* Commands: guarded under a variable context; a local declared in a guarded list takes the
  value `ite(κ, e, xd)` with a havoc `xd`; earlier declarations of a name declared again later
  are renamed (`N`), so each name has one `init`.
* `exit` under `top` drops the rest of its list; under a variable context it saves the context
  in a snapshot for its target block and sets the context false.
* After a statement that always exits, the rest of its list, already walked, is discarded: its
  registrations at enclosing blocks (exit snapshots, carried copies) are marked dead and ignored
  at the block ends.
* `block`: its body is emitted under the enclosing context, or under a fresh `rL` at top level;
  at its end the exits to it rejoin (`setReach κ (κ ∨ snapshots)`), target-less exits at top
  level are assumed away (`assume [wp$join]`), and the variables carried from always-exiting
  arms inside are merged.
* `ite c T E` after which an obligation follows is *laid out*: the guard `g := κ ∧ c`, the then
  arm under `name rT` (`rT := g`), the else arm under `¬g` (or `q ∧ ¬g`, or a fresh `rE`).
  Write-through makes the variables assigned in one arm need no merge; the variables the then
  arm assigns and the else arm reads are saved before the then arm and restored after it, so the
  else arm reads entry values, and recovered after the else arm by a copy or a merge when they
  are live.  After an arm that always exits, its assignments are undone for the continuing
  paths and delivered by one merge per variable at the innermost block its exits target.
* `ite c T E` after which no obligation follows is a *real branch*: `ite * {assume g; T}
  {assume ¬g; E}`, each arm emitted at top level, an arm without obligations dropped.

The output is a rope of items (`Rope`, `WItem`) resolved and nested once at the end (`emit`).
The phase's record is a skeleton (`SkEntry`) in loop-free order and the renamed locals (`back`).
The phase's input is the loop-free program, the types of its free variables and the names of the
enclosing program (`wpEntry`); the avoided names and the initial state are computed from it.

Key definitions: `wpEntry`, `wpBody`, `wpList`, `wpStmt`, `emit`, `WSt`, `WRes`, `WOut`. -/

namespace Imperative
namespace WP

open BigStep Strata.Util

public section

/-! ## Items of the guarded program before resolution -/

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPOps P]


/-- A type: known, or the declared type of a variable (resolved at emission, when every
    declaration has been met). -/
inductive TyRef (P : PureExpr) where
  | known (ty : P.Ty)
  | of (x : P.Ident)

/-- An expression of the guarded program before resolution: a loop-free expression with the
    renaming of its renamed free variables, a variable (annotated with its type at emission),
    a Boolean literal, or a conditional. -/
inductive WExpr (P : PureExpr) where
  | user (e : P.Expr) (ren : List (P.Ident × P.Ident))
  | var (x : P.Ident)
  | lit (b : Bool)
  | ite (c t e : WExpr P)
  deriving Inhabited

/-- `¬ a`, folded on literals. -/
@[expose] def WExpr.not : WExpr P → WExpr P
  | .lit b => .lit (!b)
  | a => .ite a (.lit false) (.lit true)

/-- `a ∨ b` as a lazy conditional. -/
@[expose] def WExpr.or (a b : WExpr P) : WExpr P := .ite a (.lit true) b

/-- `a ∧ b` as a lazy conditional. -/
@[expose] def WExpr.and (a b : WExpr P) : WExpr P := .ite a b (.lit false)

/-- An item of the guarded program before resolution: `init` (`none`: nondeterministic),
    `set`, `assume`, a run of obligations (`isCover`, label, condition, metadata) under one
    reachability, or a real branch. -/
inductive WItem (P : PureExpr) where
  | init (x : P.Ident) (ty : TyRef P) (e : Option (WExpr P))
  | set (x : P.Ident) (e : Option (WExpr P))
  | assume (l : String) (e : WExpr P) (md : MetaData P)
  | obls (r : Option (RE P)) (cs : List (Bool × String × WExpr P × MetaData P))
  | branch (t e : List (WItem P))

/-- Does the item leave the main path (a run of obligations or a real branch)? -/
@[expose] def WItem.isBranching : WItem P → Bool
  | .obls _ _ | .branch _ _ => true
  | _ => false

/-- The WP phase's record skeleton, in loop-free order: the `init` holding a havoc's value, the
    guard of an `ite` with the skeletons of its arms, a block, and one slot per emitted
    obligation. -/
inductive SkEntry (P : PureExpr) where
  | havoc (h : P.Ident)
  | ite (g : P.Ident) (t e : List (SkEntry P))
  | block (b : List (SkEntry P))
  | obl (label : String)
  deriving Inhabited

/-- The names a skeleton holds (havocs and guards), at any depth. -/
@[expose] def skNames : List (SkEntry P) → List P.Ident
  | [] => []
  | .havoc h :: rest => h :: skNames rest
  | .ite g t e :: rest => g :: (skNames t ++ skNames e ++ skNames rest)
  | .block b :: rest => skNames b ++ skNames rest
  | .obl _ :: rest => skNames rest
  termination_by sk => sizeOf sk

/-- `.obl l` occurs in the skeleton, at any depth. -/
inductive SkObl (l : String) : List (SkEntry P) → Prop where
  | head (sk : List (SkEntry P)) : SkObl l (.obl l :: sk)
  | tail (x : SkEntry P) {sk : List (SkEntry P)} : SkObl l sk → SkObl l (x :: sk)
  | iteT (g : P.Ident) {t : List (SkEntry P)} (f sk : List (SkEntry P)) :
      SkObl l t → SkObl l (.ite g t f :: sk)
  | iteE (g : P.Ident) (t : List (SkEntry P)) {f : List (SkEntry P)} (sk : List (SkEntry P)) :
      SkObl l f → SkObl l (.ite g t f :: sk)
  | block {b : List (SkEntry P)} (sk : List (SkEntry P)) :
      SkObl l b → SkObl l (.block b :: sk)

/-- The WP state. -/
structure WSt (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] where
  /-- The fresh-name counter. -/
  next : Nat
  /-- The avoided names. -/
  avoid : AvoidSet P
  /-- The current WP name of a loop-free local that a later declaration renames. -/
  nm : Std.HashMap P.Ident P.Ident := {}
  /-- The loop-free names declared later (met earlier by the walk). -/
  taken : Std.HashSet P.Ident := {}
  /-- WP name ↦ loop-free name, for the renamed locals. -/
  back : Std.HashMap P.Ident P.Ident := {}
  /-- Declared types of the names of the guarded program. -/
  tys : Std.HashMap P.Ident P.Ty := {}
  /-- Names whose type is another name's type (copies, havocs). -/
  tyOf : Std.HashMap P.Ident P.Ident := {}
  /-- The live set: names the emitted rest may read, with the clock at insertion. -/
  live : Std.HashMap P.Ident Nat := {}
  clock : Nat := 0
  /-- Snapshots of the reach at the exits to each enclosing label, newest first. -/
  pending : Std.HashMap String (List P.Ident) := {}
  /-- The depth of the innermost enclosing block with each label. -/
  labelDepth : Std.HashMap String Nat := {}
  /-- Per enclosing block depth, the clock when the walk entered its body from its end. -/
  stampAt : Std.HashMap Nat Nat := {}
  /-- Per enclosing block depth, the carried merges of always-exiting arms (variable, merged
      value, the carried copy naming the registration), newest registration first. -/
  carries : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident)) := {}
  /-- The registrations (exit snapshots, carried copies) of discarded code: the rest of a list
      after a statement that always exits. Block ends ignore them. -/
  dead : Std.HashSet P.Ident := {}

/-- The result of the WP traversal of a statement or list. -/
structure WRes (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] where
  out : Rope (WItem P) := .nil
  sk : List (SkEntry P) := []
  /-- The output contains an obligation. -/
  hasObl : Bool := false
  /-- The least target depth of an exit leaving it (target-less: 0). -/
  minT : Option Nat := none
  /-- WP names of the loop-free variables it assigns. -/
  A : Std.HashSet P.Ident := {}
  /-- WP names it reads, except the default operands of guarded writes. -/
  R : Std.HashSet P.Ident := {}
  /-- It always exits: its normal end is unreachable. -/
  ax : Bool := false
  /-- The target depths of its exits to in-region blocks outside it. -/
  tgt : LeftistHeap := .empty
  /-- It ends its main list (an `exit` at top level): the rest of the list is discarded. -/
  drop : Bool := false
  /-- The names of its registrations in `pending` and `carries` (exit snapshots, carried
      copies), at any depth. -/
  regs : Rope P.Ident := .nil

/-- The result of the WP phase: the guarded program, its record skeleton, the renamed locals
    (WP name ↦ loop-free name) and the final counter. -/
structure WOut (P : PureExpr) where
  lay : PStmts P
  sk : List (SkEntry P)
  back : List (P.Ident × P.Ident)
  next : Nat

/-- The WP monad. -/
abbrev WM (P : PureExpr) [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBool P] [HasFvar P] [HasSubstFvar P] [HasIdent P] [Hashable P.Ident] [HasFvars P] :=
  StateT (WSt P) (Except String)

/-! ## Set operations -/

/-- The union of two hash sets, inserting the smaller into the larger. -/
@[expose] def unionSet (a b : Std.HashSet P.Ident) : Std.HashSet P.Ident :=
  if a.size ≤ b.size then a.fold (fun s x => s.insert x) b else b.fold (fun s x => s.insert x) a

/-- The union of two live sets (the smaller into the larger), keeping the earliest stamp. -/
@[expose] def unionLive (a b : Std.HashMap P.Ident Nat) : Std.HashMap P.Ident Nat :=
  let ins := fun (m : Std.HashMap P.Ident Nat) (x : P.Ident) (s : Nat) =>
    match m[x]? with
    | some s' => if s < s' then m.insert x s else m
    | none => m.insert x s
  if a.size ≤ b.size then a.fold ins b else b.fold ins a

/-- The elements of `a` that are in `b`, iterating the smaller set. -/
@[expose] def interSet (a b : Std.HashSet P.Ident) : List P.Ident :=
  if a.size ≤ b.size then a.fold (fun l x => if b.contains x then x :: l else l) []
  else b.fold (fun l x => if a.contains x then x :: l else l) []

/-- The minimum of two optional depths. -/
@[expose] def minOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- Is the optional depth at most `d`? -/
@[expose] def leOpt (m : Option Nat) (d : Nat) : Bool :=
  match m with
  | some t => t ≤ d
  | none => false

/-! ## State operations -/

/-- A fresh name with base `b`. -/
@[expose] def wFresh (b : String) : WM P P.Ident := do
  let st ← get
  let (x, n) := freshIn st.avoid b st.next
  set { st with next := n }
  pure x

/-- A fresh Boolean name with base `b`. -/
@[expose] def wFreshBool (b : String) : WM P P.Ident := do
  let x ← wFresh b
  modify fun st => { st with tys := st.tys.insert x HasBool.boolTy }
  pure x

/-- A fresh name with the base and the type of the variable `x`. -/
@[expose] def wFreshLike (x : P.Ident) : WM P P.Ident := do
  let y ← wFresh (baseOf x)
  modify fun st => { st with tyOf := st.tyOf.insert y x }
  pure y

/-- `N(x)`: the current WP name of the loop-free variable `x`. -/
@[expose] def wName (x : P.Ident) : WM P P.Ident := do
  let st ← get
  match st.nm[x]? with
  | some n => pure n
  | none =>
    if st.taken.contains x then
      let (n, k) := freshIn st.avoid (baseOf x) st.next
      set { st with next := k, nm := st.nm.insert x n, back := st.back.insert n x }
      pure n
    else pure x

/-- The WP name of the variable declared by an `init x`; earlier declarations of `x` (met next
    by the walk) get another name. -/
@[expose] def wDecl (x : P.Ident) : WM P P.Ident := do
  let n ← wName x
  modify fun st => { st with nm := st.nm.erase x, taken := st.taken.insert x }
  pure n

/-- Insert names into the live set (stamped with the clock; present names keep their stamp). -/
@[expose] def liveAdd (xs : List P.Ident) : WM P Unit :=
  modify fun st =>
    let (live, clock) := xs.foldl (fun (m, c) x =>
      if m.contains x then (m, c) else (m.insert x c, c + 1)) (st.live, st.clock)
    { st with live := live, clock := clock }

/-- Remove a name from the live set. -/
@[expose] def liveDel (x : P.Ident) : WM P Unit :=
  modify fun st => { st with live := st.live.erase x }

/-- The renamed expression of a loop-free expression and the WP names it reads. -/
@[expose] def wRen (e : P.Expr) : WM P (WExpr P × List P.Ident) := do
  let xs := exprFV e
  let mut ren : List (P.Ident × P.Ident) := []
  let mut reads : List P.Ident := []
  for y in xs do
    let n ← wName y
    reads := n :: reads
    if n != y then ren := (y, n) :: ren
  pure (.user e ren, reads)

/-! ## Reach contexts -/

/-- The variables a reach context reads. -/
@[expose] def RE.vars : RE P → List P.Ident
  | .top => []
  | .name r => [r]
  | .neg g => [g]
  | .andNeg q g => [q, g]

/-- The Boolean value of a reach context. -/
@[expose] def kExpr : RE P → WExpr P
  | .top => .lit true
  | .name r => .var r
  | .neg g => (WExpr.var g).not
  | .andNeg q g => (WExpr.var q).and (WExpr.var g).not

/-- `ite(κ, t, e)`. -/
@[expose] def kIte (κ : RE P) (t e : WExpr P) : WExpr P :=
  match κ with
  | .top => t
  | .name r => .ite (.var r) t e
  | .neg g => .ite (.var g) e t
  | .andNeg q g => .ite (.var q) (.ite (.var g) e t) e

/-- `κ ∧ a`. -/
@[expose] def kAnd (κ : RE P) (a : WExpr P) : WExpr P := kIte κ a (.lit false)

/-- `κ ⟹ a`. -/
@[expose] def kImp (κ : RE P) (a : WExpr P) : WExpr P := kIte κ a (.lit true)

/-- Make the context `κ` equal `X` (`X` implies the enclosing context of `κ`). -/
@[expose] def setReach (κ : RE P) (X : WExpr P) : Rope (WItem P) :=
  match κ with
  | .top => .nil
  | .name r => .one (.set r (some X))
  | .neg g | .andNeg _ g => .one (.set g (some X.not))

/-- The disjunction of expressions, folded from the right. -/
@[expose] def disjW : List (WExpr P) → WExpr P
  | [] => .lit false
  | [a] => a
  | a :: as => a.or (disjW as)

/-- The result of a statement followed by the result of the rest of its list. -/
@[expose] def WRes.combine (a r : WRes P) : WRes P :=
  { out := a.out.app r.out, sk := a.sk ++ r.sk, hasObl := a.hasObl || r.hasObl,
    minT := minOpt a.minT r.minT, A := unionSet a.A r.A, R := unionSet a.R r.R,
    ax := a.ax || r.ax, tgt := a.tgt.merge r.tgt, drop := r.drop, regs := a.regs.app r.regs }

/-! ## The laid-out `ite` -/

/-- The saves, copies and restores of the variables `xs` around an arm: `init xs := x` before,
    `init x_c := x` and `set x := xs` after (with `x_c` the returned copy names). -/
@[expose] def saveRestore (xs : List P.Ident) :
    WM P (Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident)) := do
  let mut saves : Rope (WItem P) := .nil
  let mut copies : Rope (WItem P) := .nil
  let mut restores : Rope (WItem P) := .nil
  let mut cps : List (P.Ident × P.Ident) := []
  for x in xs do
    let s ← wFreshLike x
    let c ← wFreshLike x
    saves := saves.app (.one (.init s (.of x) (some (.var x))))
    copies := copies.app (.one (.init c (.of x) (some (.var x))))
    restores := restores.app (.one (.set x (some (.var s))))
    cps := (x, c) :: cps
  pure (saves, copies, restores, cps)

/-- Was `x` in the live set before the clock reached `t` (live after the point where the walk
    read the clock `t`)? -/
@[expose] def liveBefore (st : WSt P) (x : P.Ident) (t : Nat) : Bool :=
  match st.live[x]? with
  | some s => s < t
  | none => false

mutual
/-- The WP traversal of a statement under reach context `κ` at block depth `d`; `f`: an
    obligation follows it. -/
@[expose] def wpStmt (κ : RE P) (d : Nat) (f : Bool) : PStmt P → WM P (WRes P)
  | .cmd (.cmd (.init x ty (.det e) _)) => do
    if !f then return {}
    let (we, rd) ← wRen e
    let n ← wDecl x
    modify fun st => { st with tys := st.tys.insert n ty }
    let out ← match κ with
      | .top => pure (Rope.one (WItem.init n (.known ty) (some we)))
      | _ => do
        let xd ← wFresh (baseOf x)
        modify fun st => { st with tys := st.tys.insert xd ty }
        pure (Rope.app (.one (.init xd (.known ty) none))
          (.one (.init n (.known ty) (some (kIte κ we (.var xd))))))
    liveDel n
    liveAdd (rd ++ RE.vars κ)
    return { out := out, R := Std.HashSet.ofList rd }
  | .cmd (.cmd (.init x ty .nondet _)) => do
    if !f then return {}
    let n ← wDecl x
    modify fun st => { st with tys := st.tys.insert n ty }
    liveDel n
    return { out := .one (.init n (.known ty) none), sk := [.havoc n] }
  | .cmd (.cmd (.set x (.det e) _)) => do
    if !f then return {}
    let (we, rd) ← wRen e
    let n ← wName x
    let out ← match κ with
      | .top => do liveDel n; pure (Rope.one (WItem.set n (some we)))
      | _ => do liveAdd [n]; pure (Rope.one (WItem.set n (some (kIte κ we (.var n)))))
    liveAdd (rd ++ RE.vars κ)
    return { out := out, A := Std.HashSet.ofList [n], R := Std.HashSet.ofList rd }
  | .cmd (.cmd (.set x .nondet _)) => do
    if !f then return {}
    let n ← wName x
    let h ← wFreshLike n
    let out ← match κ with
      | .top => do liveDel n; pure (Rope.one (WItem.set n (some (.var h))))
      | _ => do
        liveAdd (n :: RE.vars κ)
        pure (Rope.one (WItem.set n (some (kIte κ (.var h) (.var n)))))
    return { out := Rope.app (.one (.init h (.of n) none)) out, sk := [.havoc h],
             A := Std.HashSet.ofList [n] }
  | .cmd (.cmd (.assume l a md)) => do
    if !f then return {}
    let (wa, rd) ← wRen a
    liveAdd (rd ++ RE.vars κ)
    return { out := .one (.assume l (kImp κ wa) md), R := Std.HashSet.ofList rd }
  | .cmd (.cmd (.assert l e md)) => do
    let (we, rd) ← wRen e
    liveAdd (rd ++ RE.vars κ)
    let r := match κ with | .top => none | κ => some κ
    return { out := .one (.obls r [(false, l, we, md)]), sk := [.obl l],
             R := Std.HashSet.ofList rd, hasObl := true }
  | .cmd (.cmd (.cover l e md)) => do
    let (we, rd) ← wRen e
    liveAdd (rd ++ RE.vars κ)
    let r := match κ with | .top => none | κ => some κ
    return { out := .one (.obls r [(true, l, we, md)]), sk := [.obl l],
             R := Std.HashSet.ofList rd, hasObl := true }
  | .cmd (.call p _ _) => throw s!"WP: call to '{p}' (run callElim first)"
  | .typeDecl _ _ => pure {}
  | .loop _ _ _ _ _ => throw "WP: loop (run loopElim first)"
  | .ite .nondet _ _ _ => throw "WP: nondeterministic guard (run nondetElim first)"
  | .exit l _ => do
    match κ with
    | .top =>
      modify fun st => { st with live := {} }
      return { drop := true }
    | _ =>
      let st ← get
      match st.labelDepth[l]? with
      | some t =>
        if !f then return { ax := true, minT := some t, tgt := .single t }
        let e ← wFreshBool "r"
        modify fun st => { st with pending := st.pending.insert l (e :: st.pending.getD l []) }
        liveAdd (RE.vars κ)
        return { out := Rope.app (.one (.init e (.known HasBool.boolTy) (some (kExpr κ))))
                   (setReach κ (.lit false)),
                 ax := true, minT := some t, tgt := .single t, regs := .one e }
      | none =>
        if !f then return { ax := true, minT := some 0 }
        return { out := setReach κ (.lit false), ax := true, minT := some 0 }
  | .block l body _ => do
    let st0 ← get
    let ld := st0.labelDepth[l]?
    let pd := st0.pending[l]?
    set { st0 with labelDepth := st0.labelDepth.insert l (d + 1),
                   pending := st0.pending.insert l [],
                   stampAt := st0.stampAt.insert (d + 1) st0.clock,
                   carries := st0.carries.insert (d + 1) [] }
    let (κB, rL?) ← match κ with
      | .top => do let r ← wFreshBool "r"; pure (RE.name r, some r)
      | κ => pure (κ, none)
    let B ← wpList κB (d + 1) f body
    let st1 ← get
    let m := ((st1.pending.getD l []).filter fun e => !st1.dead.contains e).reverse
    let C := (st1.carries.getD (d + 1) []).filter fun (_, _, k) => !st1.dead.contains k
    let ld' := match ld with
      | some v => st1.labelDepth.insert l v
      | none => st1.labelDepth.erase l
    let pd' := match pd with
      | some v => st1.pending.insert l v
      | none => st1.pending.erase l
    set { st1 with labelDepth := ld', pending := pd', carries := st1.carries.erase (d + 1) }
    let Mg : Rope (WItem P) :=
      C.foldl (fun acc (x, v, _) => acc.app (.one (.set x (some v)))) .nil
    let J : Rope (WItem P) :=
      if !f then .nil
      else match rL? with
        | some rL =>
          if leOpt B.minT d then
            .one (.assume joinLabel (disjW (.var rL :: m.map .var)) .empty)
          else .nil
        | none =>
          if m.isEmpty then .nil else setReach κ (disjW (kExpr κ :: m.map .var))
    let tail := (B.out.app Mg).app J
    let out := match rL? with
      | some rL =>
        if tail.isNil then .nil
        else Rope.app (.one (.init rL (.known HasBool.boolTy) (some (.lit true)))) tail
      | none => tail
    liveAdd (RE.vars κ)
    return { out := out, sk := [.block B.sk], hasObl := B.hasObl,
             minT := if leOpt B.minT d then B.minT else none,
             A := C.foldl (fun s (x, _, _) => s.insert x) B.A, R := B.R,
             ax := B.ax && m.isEmpty, tgt := B.tgt.popEq (d + 1), regs := B.regs }
  | .ite (.det c) tss ess _ => do
    if f then wpIteLaid κ d c tss ess else wpIteReal κ d c tss ess
  termination_by s => 2 * sizeOf s + 1

/-- The WP traversal of a laid-out `ite c T E` (an obligation follows it). -/
@[expose] def wpIteLaid (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P) :
    WM P (WRes P) := do
  let (wc, rdc) ← wRen c
  let g ← wFreshBool "g"
  let rT ← wFreshBool "r"
  let (κE, rE?) ← match κ with
    | .top => pure (RE.neg g, none)
    | .name q => pure (RE.andNeg q g, none)
    | _ => do let r ← wFreshBool "r"; pure (RE.name r, some r)
  let t0 := (← get).clock
  let E ← wpList κE d true ess
  let T ← wpList (.name rT) d true tss
  let st ← get
  -- step 3: the variables the then arm assigns and the else arm reads
  let M := if T.ax then [] else interSet T.A E.R
  let (savesT3, copiesT3, restoresT3, cpsT3) ← saveRestore M
  let liveM := cpsT3.filter fun (p : P.Ident × P.Ident) => liveBefore st p.1 t0
  -- step 3b: the assignments of always-exiting arms
  let CT := if T.ax then T.A.fold (fun l x =>
      if liveBefore st x t0 || E.R.contains x then x :: l else l) [] else []
  let CE := if E.ax then E.A.fold (fun l x => if liveBefore st x t0 then x :: l else l) [] else []
  let (savesT, copiesT, restoresT, cpsT) ← saveRestore CT
  let (savesE, copiesE, restoresE, cpsE) ← saveRestore CE
  let carryT := match T.tgt.max? with
    | some t => cpsT.filter fun (p : P.Ident × P.Ident) => liveBefore st p.1 (st.stampAt.getD t 0)
    | none => []
  let carryE := match E.tgt.max? with
    | some t => cpsE.filter fun (p : P.Ident × P.Ident) => liveBefore st p.1 (st.stampAt.getD t 0)
    | none => []
  let regs : Rope P.Ident :=
    (T.regs.app E.regs).app (Rope.ofList (carryT.map (·.2) ++ carryE.map (·.2)))
  let needMerge := liveM.any fun (x, _) => E.A.contains x && !E.ax
  let needGm := needMerge || !carryT.isEmpty ||
    (!carryE.isEmpty && match κ with | .top | .name _ => true | _ => false)
  let gm? ← if needGm then do let x ← wFreshBool "g"; pure (some x) else pure none
  let qm? ← match κ, carryE.isEmpty with
    | .name _, false => do let x ← wFreshBool "r"; pure (some x)
    | _, _ => pure none
  let rEm? ← match rE?, carryE.isEmpty with
    | some _, false => do let x ← wFreshBool "r"; pure (some x)
    | _, _ => pure none
  let gmE : WExpr P := match gm? with | some x => .var x | none => .lit false
  let mergesL : Rope (WItem P) := liveM.foldl (fun acc (x, xT) =>
    acc.app (.one (.set x (some (if E.A.contains x && !E.ax then .ite gmE (.var xT) (.var x)
      else .var xT))))) .nil
  -- register, at the exit target of each always-exiting arm, the merges of its carried copies,
  -- each selecting the copy under the condition that the arm was taken (`eT`, `eE`)
  let eT : WExpr P := gmE
  let eE : WExpr P := match κ, qm?, rEm? with
    | .top, _, _ => gmE.not
    | .name _, some qm, _ => (WExpr.var qm).and gmE.not
    | _, _, some rEm => .var rEm
    | _, _, _ => .lit false
  if let some t := T.tgt.max? then
    modify fun st =>
      let l := carryT.foldl (fun l (x, xB) => (x, .ite eT (.var xB) (.var x), xB) :: l)
        (st.carries.getD t [])
      { st with carries := st.carries.insert t l }
  if let some t := E.tgt.max? then
    modify fun st =>
      let l := carryE.foldl (fun l (x, xB) => (x, .ite eE (.var xB) (.var x), xB) :: l)
        (st.carries.getD t [])
      { st with carries := st.carries.insert t l }
  -- the reach update
  let U : Rope (WItem P) :=
    if leOpt T.minT d || leOpt E.minT d then
      let X := (WExpr.var rT).or (kExpr κE)
      match κ with
      | .top => .one (.assume joinLabel X .empty)
      | κ => setReach κ X
    else .nil
  let bool := TyRef.known (P := P) HasBool.boolTy
  let rTi : Rope (WItem P) := if T.out.isNil && U.isNil then .nil
    else .one (.init rT bool (some (.var g)))
  let gmi : Rope (WItem P) := match gm? with
    | some x => .one (.init x bool (some (.var g))) | none => .nil
  let qmi : Rope (WItem P) := match κ, qm? with
    | .name q, some x => .one (.init x bool (some (.var q))) | _, _ => .nil
  let rEi : Rope (WItem P) := match rE? with
    | some r => if E.out.isNil && U.isNil && rEm?.isNone then .nil
      else .one (.init r bool (some (kAnd κ (WExpr.var g).not)))
    | none => .nil
  let rEmi : Rope (WItem P) := match rE?, rEm? with
    | some r, some x => .one (.init x bool (some (.var r))) | _, _ => .nil
  let body : Rope (WItem P) :=
    [rTi, gmi, qmi, savesT3, savesT, T.out, copiesT3, copiesT, restoresT3, restoresT, rEi, rEmi,
      savesE, E.out, copiesE, restoresE, mergesL, U].foldl Rope.app .nil
  if body.isNil then
    return { A := {}, R := {}, minT := minOpt T.minT E.minT, tgt := T.tgt.merge E.tgt,
             ax := T.ax && E.ax, regs := regs }
  liveAdd (rdc ++ RE.vars κ)
  let out := Rope.app (.one (.init g bool (some (kAnd κ wc)))) body
  return { out := out, sk := [.ite g T.sk E.sk], hasObl := T.hasObl || E.hasObl,
           minT := minOpt T.minT E.minT,
           A := unionSet (if T.ax then {} else T.A) (if E.ax then {} else E.A),
           R := unionSet (unionSet T.R E.R) (Std.HashSet.ofList rdc),
           ax := T.ax && E.ax, tgt := T.tgt.merge E.tgt, regs := regs }
  termination_by 2 * sizeOf tss + 2 * sizeOf ess + 2

/-- The WP traversal of an `ite c T E` after which no obligation follows: a real branch whose
    arms are emitted at top level. -/
@[expose] def wpIteReal (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P) :
    WM P (WRes P) := do
  let st0 ← get
  set { st0 with live := {}, labelDepth := {}, pending := {} }
  let E ← wpList .top d false ess
  let LE := (← get).live
  modify fun st => { st with live := {} }
  let T ← wpList .top d false tss
  let LT := (← get).live
  let live := unionLive (unionLive LT LE) st0.live
  modify fun st => { st with labelDepth := st0.labelDepth, pending := st0.pending, live := live }
  if !T.hasObl && !E.hasObl then return {}
  let (wc, rdc) ← wRen c
  let g ← wFreshBool "g"
  liveAdd (rdc ++ RE.vars κ)
  let bool := TyRef.known (P := P) HasBool.boolTy
  let gi : Rope (WItem P) := .one (.init g bool (some (kAnd κ wc)))
  let aT : Rope (WItem P) := .one (.assume reachLabel (.var g) .empty)
  let aE : Rope (WItem P) := .one (.assume reachLabel (kAnd κ (WExpr.var g).not) .empty)
  let out : Rope (WItem P) :=
    if T.hasObl && E.hasObl then
      gi.app (.one (.branch (aT.app T.out).toList (aE.app E.out).toList))
    else if T.hasObl then (gi.app aT).app T.out
    else (gi.app aE).app E.out
  return { out := out, sk := [.ite g T.sk E.sk], hasObl := true,
           A := unionSet T.A E.A, R := unionSet (unionSet T.R E.R) (Std.HashSet.ofList rdc),
           regs := T.regs.app E.regs }
  termination_by 2 * sizeOf tss + 2 * sizeOf ess + 2

/-- The WP traversal of a statement list under reach context `κ` at block depth `d`; `fEnd`:
    an obligation follows the list.  The rest is processed before the head. -/
@[expose] def wpList (κ : RE P) (d : Nat) (fEnd : Bool) : PStmts P → WM P (WRes P)
  | [] => pure {}
  | s :: rest => do
    let r ← wpList κ d fEnd rest
    let a ← wpStmt κ d (r.hasObl || (fEnd && !r.drop)) s
    if a.drop then return a
    if a.ax then
      modify fun st => { st with dead := r.regs.toList.foldl (·.insert ·) st.dead }
      return a
    return a.combine r
  termination_by ss => 2 * sizeOf ss
end

/-! ## Emission -/

/-- The declared type of a name of the guarded program. -/
@[expose] def tyOfName (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident)
    (x : P.Ident) : Except String P.Ty :=
  match tys[x]? with
  | some ty => pure ty
  | none =>
    match tyOf[x]? >>= (tys[·]?) with
    | some ty => pure ty
    | none => throw s!"WP: no type known for variable '{WPOps.name x}'"

/-- Resolve an expression of the guarded program: variables annotated with their types, the
    renaming of a loop-free expression applied by `substFn` with a hash map built once. -/
@[expose] def resolveE (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident) :
    WExpr P → Except String P.Expr
  | .user e [] => pure e
  | .user e ren => do
    let h : Std.HashMap P.Ident P.Expr ← ren.foldlM (init := {}) fun h (y, y') => do
      pure (h.insert y (HasFvar.mkVar y' (some (← tyOfName tys tyOf y'))))
    pure (WPOps.substFn e (fun y => h[y]?))
  | .var x => do pure (HasFvar.mkVar x (some (← tyOfName tys tyOf x)))
  | .lit b => pure (if b then tt else ff)
  | .ite c t e => do
    pure (WPOps.ite (← resolveE tys tyOf c) (← resolveE tys tyOf t) (← resolveE tys tyOf e))

/-- Resolve an optional expression. -/
@[expose] def resolveOE (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident) :
    Option (WExpr P) → Except String (ExprOrNondet P)
  | some e => do pure (.det (← resolveE tys tyOf e))
  | none => pure .nondet

mutual
/-- Resolve the items of a guarded program into flat items (`Item`). -/
@[expose] def resolveItems (tys : Std.HashMap P.Ident P.Ty)
    (tyOf : Std.HashMap P.Ident P.Ident) : List (WItem P) → Except String (List (Item P))
  | [] => pure []
  | it :: rest => do
    let a ← resolveItem tys tyOf it
    let r ← resolveItems tys tyOf rest
    pure (a :: r)
/-- Resolve one item. -/
@[expose] def resolveItem (tys : Std.HashMap P.Ident P.Ty)
    (tyOf : Std.HashMap P.Ident P.Ident) : WItem P → Except String (Item P)
  | .init x ty e => do
    let ty ← match ty with
      | .known ty => pure ty
      | .of y => tyOfName tys tyOf y
    pure (.plain (mkInit x ty (← resolveOE tys tyOf e)))
  | .set x e => do pure (.plain (.cmd (.cmd (.set x (← resolveOE tys tyOf e) .empty))))
  | .assume l e md => do pure (.plain (.cmd (.cmd (.assume l (← resolveE tys tyOf e) md))))
  | .obls r cs => do
    let cs ← cs.mapM fun (isCover, l, e, md) => do
      let e ← resolveE tys tyOf e
      pure (if isCover then (.cmd (.cmd (.cover l e md)) : PStmt P)
        else .cmd (.cmd (.assert l e md)))
    pure (.obls r cs)
  | .branch t e => do
    pure (.branch (← resolveItems tys tyOf t) (← resolveItems tys tyOf e))
end

/-- Merge adjacent runs of obligations under equal reachabilities. -/
@[expose] def mergeObls : List (Item P) → List (Item P)
  | [] => []
  | .obls r cs :: rest =>
    match mergeObls rest with
    | .obls r' cs' :: rest' => if r = r' then .obls r (cs ++ cs') :: rest'
      else .obls r cs :: .obls r' cs' :: rest'
    | rest' => .obls r cs :: rest'
  | .branch t e :: rest => .branch (mergeObls t) (mergeObls e) :: mergeObls rest
  | it :: rest => it :: mergeObls rest

/-- The guarded program of the items: resolved, adjacent obligation runs merged, nested. -/
@[expose] def emit (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident)
    (s : Rope (WItem P)) : Except String (PStmts P) := do
  pure (nest (mergeObls (← resolveItems tys tyOf s.toList)))

/-- **The WP phase.**  The guarded program of the loop-free list `ss`, its record skeleton, the
    renamed locals and the final counter, from the counter, avoided names and parameter types of
    `st`. -/
@[expose] def wpBody (st : FreshSt P) (ss : PStmts P) : Except String (WOut P) := do
  let tys := st.tys.foldr (fun (x, ty) m => m.insert x ty) {}
  let st0 : WSt P := { next := st.next, avoid := st.avoid, tys := tys }
  let (r, st1) ← (wpList .top 0 false ss).run st0
  let lay ← emit st1.tys st1.tyOf r.out
  pure ⟨lay, r.sk, st1.back.toList, st1.next⟩

/-- **The WP phase of a loop-free list** `ss` whose free variables have the types `tys`, its fresh
    names avoiding `inputAvoid G tys ss`, from the counter `0`. -/
@[expose] def wpEntry (G : IdSet P) (tys : Tys P) (ss : PStmts P) : Except String (WOut P) :=
  wpBody ⟨0, inputAvoid G tys ss, tys⟩ ss

end -- public section

end WP
end Imperative
