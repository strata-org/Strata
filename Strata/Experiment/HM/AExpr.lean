/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Expr

/-! ## Annotated Expressions for Hindley-Milner

Annotations placed only where the type is ambiguous.
-/

namespace HM

inductive AExpr where
  | bvar  : Nat → AExpr
  | fvar  : Ty → String → AExpr
  | app   : Ty → Ty → AExpr → AExpr → AExpr
  | abs   : Ty → AExpr → AExpr
  | op    : Ty → String → AExpr
  | const : Const → AExpr
  | ite   : Ty → AExpr → AExpr → AExpr → AExpr
  | eq    : Ty → AExpr → AExpr → AExpr
  | quant : QuantKind → Ty → AExpr → AExpr
  deriving Inhabited, Repr

/-- Strip annotations to recover the original `Expr`. -/
def AExpr.erase : AExpr → Expr
  | .bvar n         => .bvar n
  | .fvar _ x       => .fvar x
  | .app _ _ f a    => .app f.erase a.erase
  | .abs _ e        => .abs e.erase
  | .op _ s         => .op s
  | .const c        => .const c
  | .ite _ c t e    => .ite c.erase t.erase e.erase
  | .eq _ a b       => .eq a.erase b.erase
  | .quant q _ e    => .quant q e.erase

/-- Open: replace `bvar k` with `fvar x` (with type annotation `ty`). -/
def AExpr.varOpen (k : Nat) (ty : Ty) (x : String) : AExpr → AExpr
  | .bvar n         => if n = k then .fvar ty x else .bvar n
  | .fvar t y       => .fvar t y
  | .app t₁ t₂ f a => .app t₁ t₂ (f.varOpen k ty x) (a.varOpen k ty x)
  | .abs t e        => .abs t (e.varOpen (k + 1) ty x)
  | .op t s         => .op t s
  | .const c        => .const c
  | .ite t c th el  => .ite t (c.varOpen k ty x) (th.varOpen k ty x) (el.varOpen k ty x)
  | .eq t a b       => .eq t (a.varOpen k ty x) (b.varOpen k ty x)
  | .quant q τ e    => .quant q τ (e.varOpen (k + 1) ty x)

/-- Close: replace `fvar x` with `bvar k`. -/
def AExpr.varClose (k : Nat) (x : String) : AExpr → AExpr
  | .bvar n         => .bvar n
  | .fvar t y       => if y = x then .bvar k else .fvar t y
  | .app t₁ t₂ f a => .app t₁ t₂ (f.varClose k x) (a.varClose k x)
  | .abs t e        => .abs t (e.varClose (k + 1) x)
  | .op t s         => .op t s
  | .const c        => .const c
  | .ite t c th el  => .ite t (c.varClose k x) (th.varClose k x) (el.varClose k x)
  | .eq t a b       => .eq t (a.varClose k x) (b.varClose k x)
  | .quant q τ e    => .quant q τ (e.varClose (k + 1) x)

end HM
