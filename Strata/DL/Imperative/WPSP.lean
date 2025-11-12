/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.PureExpr
import Strata.DL.Imperative.BasicBlock
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.Passify

namespace Imperative

mutual

def isDesugaredStmt : (Stmt P C) → Bool
| .cmd _ => true
| .block _ ⟨ bss ⟩ _ => isDesugaredStmts bss
| .ite _ ⟨ tss ⟩ ⟨ ess ⟩ _ =>
  isDesugaredStmts tss && isDesugaredStmts ess
| .loop _ _ _ _ _ => false
| .goto _ _ => false

def isDesugaredStmts : List (Stmt P C) → Bool
| [] => true
| s :: ss => isDesugaredStmt s && isDesugaredStmts ss

end

def DesugaredStmt (P : PureExpr) (C : Type) := { s : Stmt P C // isDesugaredStmt s }

def FreshType (P : PureExpr) := P.Ident → P.Ident
def SubstType (P : PureExpr) := P.Expr → P.Ident → P.Expr → P.Expr

def wpCmd
  [HasAnd P] [HasImp P] [HasFvar P] :
  FreshType P → SubstType P → Cmd P → P.Expr → P.Expr
| _, _, .assert _ p _, q => HasAnd.and p q
| _, _, .assume _ p _, q => HasImp.imp p q
| ν, σ, .havoc x _, q    => σ q x (HasFvar.mkFvar (ν x))
| _, σ, .set x e _, q    => σ q x e
| _, σ, .init x _ e _, q => σ q x e

def wpPassiveCmd [HasAnd P] [HasImp P]: (PassiveCmd P) → P.Expr → P.Expr
| ⟨ .assert _ p _, _ ⟩, q => HasAnd.and p q
| ⟨ .assume _ p _, _ ⟩, q => HasImp.imp p q

def wpPassiveCmds [HasAnd P] [HasImp P]: List (PassiveCmd P) → P.Expr → P.Expr
| cs, q => cs.foldr wpPassiveCmd q

variable {Label : Type}

def labelToFVar {P : PureExpr} [HasFvar P] : Label → P.Expr := sorry

def wpPassiveBasicBlock [HasEq P] [HasFvar P] [HasAnd P] [HasImp P] [HasBool P]: PassiveBasicBlock Label P → P.Expr
| ⟨ l, cs, tc ⟩ =>
  let wpVar := labelToFVar l
  let targetVars := match tc with | .goto ls _ => ls.map labelToFVar
  let q := targetVars.foldl HasAnd.and HasBool.tt
  HasEq.eq wpVar (wpPassiveCmds cs q)

def wpPassiveCFG [HasEq P] [HasFvar P] [HasAnd P] [HasImp P] [HasBool P] (cfg : CFG Label (PassiveBasicBlock Label P)) : P.Expr :=
 HasImp.imp ((cfg.blocks.map wpPassiveBasicBlock).foldl HasAnd.and HasBool.tt) (labelToFVar cfg.entry)

mutual

def wpPassiveStmt {P : PureExpr} [HasAnd P] [HasImp P]: Stmt P (PassiveCmd P) → P.Expr → Option P.Expr
| .cmd c, q => wpPassiveCmd c q
| .ite c ⟨ tss ⟩ ⟨ ess ⟩ _, q => do
  let tq ← wpPassiveStmts tss q
  let eq ← wpPassiveStmts ess q
  HasAnd.and (HasImp.imp c tq) (HasImp.imp c eq)
| .block _ ⟨ bss ⟩ _, q => wpPassiveStmts bss q
| .loop c m i b _, q => none
| .goto _ _, q => none -- TODO: look up?

def wpPassiveStmts [HasAnd P] [HasImp P]: List (Stmt P (PassiveCmd P)) → P.Expr → Option P.Expr
| [], q => q
| s :: ss, q => do
  wpPassiveStmt s (← wpPassiveStmts ss q)

end

def wpPassiveBlock [HasAnd P] [HasImp P]: Block P (PassiveCmd P) → P.Expr → Option P.Expr
| b, q => wpPassiveStmts b.ss q

theorem desugaredWpSome
  {P : PureExpr}
  [HasAnd P] [HasImp P]
  {s : Stmt P (PassiveCmd P)} {q : P.Expr}
  (isDesugared : isDesugaredStmt s) :
  (wpPassiveStmt s q).isSome := by
  sorry
