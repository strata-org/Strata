/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.PureExpr
meta import Strata.DL.Imperative.Cmd
meta import Strata.Util.ListMap

meta section

/-! # Tests for the identifier-renaming machinery

Pins the two key semantic choices of `renameLookup` / `substMapOf` /
`substFvarManyExpr`, both of which a naive left-fold of single substitutions
would silently break:

* **first match** — `renameLookup` resolves a source through the FIRST matching
  pair, so a duplicated source maps to its first target;
* **simultaneous (non-cascading)** — renaming `[(x, y), (y, z)]` in `x + y`
  gives `y + z`, NOT `z + z`: the `y` introduced by the first rename is not
  itself re-renamed by the second pair. -/

namespace RenameTest
open Imperative

/-- A tiny expression tree: a free variable, a binary `+`, or an opaque literal.
    Rich enough to observe simultaneous substitution without cascading. -/
inductive Expr where
  | var (name : String)
  | add (l r : Expr)
  | lit
  deriving DecidableEq, Repr, Inhabited

/-- Simultaneous single-pass substitution: each `var` is replaced by the FIRST
    matching entry's expression; the result is NOT re-traversed, so a target that
    happens to be another entry's source is left alone. -/
def Expr.substAll (e : Expr) (m : List (String × Expr)) : Expr :=
  match e with
  | .var x => (Map.find? m x).getD (.var x)
  | .add l r => .add (l.substAll m) (r.substAll m)
  | .lit => .lit

abbrev MiniPureExpr : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := Expr,
    Ty := Unit,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    Factory := Unit,
    eval := fun _ _ e => some e }

instance : HasFvar MiniPureExpr where
  mkFvar x := .var x
  mkTypedFvar x _ := .var x
  getFvar e := match e with | .var x => some x | _ => none

instance : HasSubstFvar MiniPureExpr where
  substFvar e x e' := e.substAll [(x, e')]
  substFvars e m := e.substAll m
  renameFvars e subst := e.substAll (subst.map (fun p => (p.1, Expr.var p.2)))

---------------------------------------------------------------------

/-! ## `renameLookup` — first-match resolution -/

-- First match: with `[(x, y), (y, z)]`, `x` resolves to `y` (NOT cascading to `z`).
/-- info: "y" -/
#guard_msgs in
#eval renameLookup (P := MiniPureExpr) [("x", "y"), ("y", "z")] "x"

-- The second source resolves to its own target (`y ↦ z`); combined with the case
-- above, a fold-based cascade (`x ↦ z`) is ruled out.
/-- info: "z" -/
#guard_msgs in
#eval renameLookup (P := MiniPureExpr) [("x", "y"), ("y", "z")] "y"

-- Duplicated source: the FIRST pair wins, so `x ↦ a` (not `b`).
/-- info: "a" -/
#guard_msgs in
#eval renameLookup (P := MiniPureExpr) [("x", "a"), ("x", "b")] "x"

-- Identity off the sources.
#guard renameLookup (P := MiniPureExpr) [("x", "y")] "w" == "w"

/-! ## `substMapOf` — lookup returns the target as a free variable -/

-- On a source, `substMapOf` maps through `Map.find?` to the renamed target as an `fvar`.
#guard Map.find? (substMapOf (P := MiniPureExpr) [("x", "y"), ("y", "z")]) "x"
         == some (Expr.var "y")

-- Off the sources, `substMapOf` lookup is `none`.
#guard Map.find? (substMapOf (P := MiniPureExpr) [("x", "y")]) "w" == none

/-! ## `substFvarManyExpr` — simultaneous, non-cascading expression rewrite -/

-- The key design choice: renaming `[(x, y), (y, z)]` in `x + y` gives `y + z`, NOT
-- `z + z`. A left fold of single substitutions would cascade the fresh `y` through
-- the second pair and wrongly produce `z + z`.
#guard substFvarManyExpr (P := MiniPureExpr) [("x", "y"), ("y", "z")]
         (.add (.var "x") (.var "y")) == Expr.add (.var "y") (.var "z")

-- A variable absent from the rename list is left unchanged.
#guard substFvarManyExpr (P := MiniPureExpr) [("x", "y")] (.var "w") == Expr.var "w"

end RenameTest

end
