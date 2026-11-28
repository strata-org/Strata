/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.LExprEval

/-! # The facts a path condition gives

The values the assumptions on a path give variables and terms, the definitions
`x := e` on the path, and candidate witnesses for existentials, with the operations
that record, look up and forget them. A fact `a == b` is oriented so that a value, or
otherwise a constructor application, replaces the other side (`orient`).

Equality simplification records its facts here. Contextual rewriting uses `orient`,
`isReplacement`, `defDepth` and `HashOf`. The module imports no pipeline phase.
-/

namespace Core.EqualitySimplification

open Lambda Imperative

@[expose] public section

/-- The facts a path condition gives. A variable or term mapped to `none` has two
    different values, and is left alone. -/
structure Facts where
  /-- Values the assumptions give variables. -/
  vars : Std.HashMap CoreIdent (Option Expression.Expr) := {}
  /-- Values the assumptions give terms other than variables, bucketed by
      `LExpr.hashExpr`. Neither a term nor its value contains a bound variable. -/
  terms : Std.HashMap UInt64 (List (Expression.Expr × Option Expression.Expr)) := {}
  /-- The path condition's definitions `x := e`. A definition is dropped when its
      variable is defined again or written, so each variable has at most one. -/
  defs : Std.HashMap CoreIdent Expression.Expr := {}
  /-- Whether an assumption already folded to `false` under the earlier facts. Goals on
      such a path are left for the solver, which finds them valid, instead of being
      folded to a `false` that the facts' inconsistency produced. This is a best-effort
      check: an inconsistency that folding does not expose, such as `f(x) == 3` and
      `f(1) == 4` under `x == 1`, leaves `dead` unset, and a goal on that path can still
      fold to `false`. -/
  dead : Bool := false
  /-- The arguments `v` of the facts `f(v) ↦ true`, keyed by `f`'s name and
      type annotation: candidate witnesses for an existential with trigger
      `f(x)`. -/
  hints : Std.HashMap (String × LMonoTy) (List Expression.Expr) := {}

namespace Facts

def isEmpty (fs : Facts) : Bool := fs.vars.isEmpty && fs.terms.isEmpty && fs.defs.isEmpty

/-- Map `x` to `v` in `m`, or to `none` if it already has a different value. -/
def insertUnique (m : Std.HashMap CoreIdent (Option Expression.Expr)) (x : CoreIdent)
    (v : Expression.Expr) : Std.HashMap CoreIdent (Option Expression.Expr) :=
  match m.get? x with
  | none => m.insert x (some v)
  | some (some v') => if v'.beqIgnoringMetadata v then m else m.insert x none
  | some none => m

/-- Record `v` as a candidate witness for `f` from the fact `f(v) ↦ true`. -/
def addHint (fs : Facts) (lhs rhs : Expression.Expr) : Facts :=
  match lhs, rhs with
  | .app _ (.op _ f (some fty)) v, .const _ (.boolConst true) =>
    let key := (f.name, fty)
    { fs with hints := fs.hints.insert key (v :: fs.hints.getD key []) }
  | _, _ => fs

/-- Record that `lhs` equals `rhs`. A variable or term given two different values is
    dropped, as `insertUnique` does, and a term or value with a bound variable is not
    recorded. -/
def insert (fs : Facts) (lhs rhs : Expression.Expr) : Facts :=
  if rhs.hasBVar then fs else
  match lhs with
  | .fvar _ x _ => { fs with vars := insertUnique fs.vars x rhs }
  | _ =>
    if lhs.hasBVar then fs else
    let fs := fs.addHint lhs rhs
    let h := LExpr.hashExpr lhs
    let bucket := fs.terms.getD h []
    match bucket.find? (·.1.beqIgnoringMetadata lhs) with
    | none => { fs with terms := fs.terms.insert h ((lhs, some rhs) :: bucket) }
    | some (_, some v) =>
      if v.beqIgnoringMetadata rhs then fs
      else
        let bucket := bucket.map fun (k, v) => if k.beqIgnoringMetadata lhs then (k, none) else (k, v)
        { fs with terms := fs.terms.insert h bucket }
    | some (_, none) => fs

/-- The value recorded for the term `e`, whose hash is `h`. -/
def lookupTerm (fs : Facts) (e : Expression.Expr) (h : UInt64) : Option Expression.Expr :=
  (fs.terms.get? h).bind fun bucket => (bucket.find? (·.1.beqIgnoringMetadata e)).bind (·.2)

/-- `fs` without the facts that mention one of `xs`: their values, definitions
    and recorded terms, as on either side. -/
def forget (fs : Facts) (xs : List CoreIdent) : Facts :=
  if xs.isEmpty then fs else
  let xs : Std.HashSet CoreIdent := Std.HashSet.ofList xs
  let mentions (e : Expression.Expr) : Bool :=
    (HasFvars.getFvars (P := Expression) e).any (xs.contains ·)
  let keep (x : CoreIdent) (v : Option Expression.Expr) : Bool :=
    !xs.contains x && !(v.map mentions).getD false
  let nonEmpty {α : Type} (l : List α) : Option (List α) :=
    if l.isEmpty then none else some l
  { fs with
    vars := fs.vars.filter keep
    defs := fs.defs.filter fun x v => keep x (some v)
    terms := fs.terms.filterMap fun _ bucket =>
      nonEmpty (bucket.filter fun (k, v) =>
        !mentions k && !(v.map mentions).getD false)
    hints := fs.hints.filterMap fun _ vs =>
      nonEmpty (vs.filter (!mentions ·)) }

/-- The definition of `x`, if the program gives it exactly one. -/
def defOf? (fs : Facts) (x : CoreIdent) : Option Expression.Expr :=
  fs.defs.get? x

/-- `e` read through up to `n` definitions while it is a defined variable. -/
def seeThrough (fs : Facts) : Nat → Expression.Expr → Expression.Expr
  | n + 1, e@(.fvar _ x _) =>
    match fs.defOf? x with
    | some d => fs.seeThrough n d
    | none => e
  | _, e => e

end Facts

variable (F : @Lambda.Factory CoreLParams)

/-- Whether `e` may replace a term equal to it: a value, or a constructor
    application, which is what lets a destructor or tester reduce. -/
def isReplacement (e : Expression.Expr) : Bool :=
  LExpr.isValue F e || LExpr.isConstrApp F e

/-- The fact `l == r` oriented as `(lhs, rhs)`, so that `rhs` replaces `lhs`. Each
    side is read through its definitions: a value replaces a non-value, and
    otherwise a constructor application replaces a term that is not one. -/
def orient (l r : Expression.Expr) (l' r' : Expression.Expr) :
    Option (Expression.Expr × Expression.Expr × Expression.Expr) :=
  -- `l'` and `r'` are `l` and `r` read through their definitions; the result names
  -- the side to replace in both forms, then its replacement.
  match LExpr.isValue F l', LExpr.isValue F r' with
  | false, true => some (l, l', r')
  | true, false => some (r, r', l')
  | true, true => none
  | false, false =>
    match LExpr.isConstrApp F l', LExpr.isConstrApp F r' with
    | false, true => some (l, l', r')
    | true, false => some (r, r', l')
    | _, _ => none

/-- How many definitions are read through in a row, which bounds the work a chain of
    definitions costs. -/
def defDepth : Nat := 16

/-- The hash `LExpr.hashExpr e`, which `Facts.insert` keys terms by, computed from the
    hashes of `e`'s children. The equation is checked by the type, so that a change to
    either hash cannot silently make lookups miss. -/
abbrev HashOf (e : Expression.Expr) := { h : UInt64 // h = LExpr.hashExpr e }

end -- public section

end Core.EqualitySimplification
