/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module



public import Strata.Languages.Core.Identifiers
public import Std.Data.HashSet

namespace Core
public section
---------------------------------------------------------------------

open Std (ToFormat Format format)
open Lambda

/-!
## Axioms

Axioms are propositions assumed to be true throughout a Strata Core program.
They are passed on as assumptions to the SMT solver during VC generation. It's
the responsibility of the user to ensure that they are consistent.
-/

structure Axiom where
  name : CoreLabel
  e : LExpr CoreLParams.mono
  deriving BEq, DecidableEq

instance : ToFormat (CoreLParams.mono : LExprParamsT).base.Identifier :=
  show ToFormat CoreIdent from inferInstance

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

def Axiom.eraseTypes (a : Axiom) : Axiom :=
  { a with e := a.e.eraseTypes }

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

/-!
## Lemmas

A lemma is a proposition, written like an axiom, that must be proved. Each
lemma yields one proof obligation whose assumptions are the axioms and
`distinct` facts declared before it, as for an assertion in a procedure.
A lemma is never assumed when checking other declarations.

A lemma may have type parameters, which may occur free in its formula. It must
hold at every instantiation of them.
-/

structure Lemma where
  name : CoreLabel
  typeArgs : List TyIdentifier := []
  e : LExpr CoreLParams.mono
  deriving BEq, DecidableEq

/-- Replace each free variable named `x` by the bound variable of a binder `k`
levels up. Unlike `LExpr.varClose`, the match ignores type annotations, which
are not yet resolved when lemmas are generated before type checking. -/
private def closeVarByName (k : Nat) (x : CoreIdent) :
    LExpr CoreLParams.mono → LExpr CoreLParams.mono
  | .fvar m y ty => if y == x then .bvar m k else .fvar m y ty
  | .abs m n ty e => .abs m n ty (closeVarByName (k + 1) x e)
  | .quant m qk n ty tr e =>
    .quant m qk n ty (closeVarByName (k + 1) x tr) (closeVarByName (k + 1) x e)
  | .app m a b => .app m (closeVarByName k x a) (closeVarByName k x b)
  | .ite m c t e => .ite m (closeVarByName k x c) (closeVarByName k x t) (closeVarByName k x e)
  | .eq m a b => .eq m (closeVarByName k x a) (closeVarByName k x b)
  | e => e

/-- Quantify `e` universally over `binders`, outermost first: the free
occurrences of each binder's name become bound by it. -/
def Lemma.forallOver (binders : List (CoreIdent × LMonoTy)) (e : LExpr CoreLParams.mono) :
    LExpr CoreLParams.mono :=
  binders.foldr (init := e) fun (x, ty) body =>
    .quant () .all x.name (some ty) (LExpr.noTrigger ()) (closeVarByName 0 x body)

/-- `label`, or `label_k` for the smallest `k ≥ 1` that makes it differ from
every name in `taken`. Generated lemmas are named this way, so that they never
clash with a declaration of the program or with each other. -/
def Lemma.freshName (taken : Std.HashSet String) (label : String) : String :=
  if !taken.contains label then label
  else
    let rec go (k : Nat) (fuel : Nat) : String :=
      match fuel with
      | 0 => s!"{label}_{k}"
      | fuel + 1 =>
        let n := s!"{label}_{k}"
        if taken.contains n then go (k + 1) fuel else n
    go 1 taken.size

def Lemma.eraseTypes (l : Lemma) : Lemma :=
  { l with e := l.e.eraseTypes }

instance : ToFormat Lemma where
  format l :=
    let targs := if l.typeArgs.isEmpty then f!"" else f!" <{Std.Format.joinSep (l.typeArgs.map format) ", "}>"
    f!"lemma {l.name}{targs}: {l.e};"

end
---------------------------------------------------------------------
