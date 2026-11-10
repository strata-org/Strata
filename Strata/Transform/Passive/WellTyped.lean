/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Typed

/-! # Well-typed statement lists

A statement list is *well typed* under the typing `Γ` of the names in scope at its entry
(`Block.WellTyped`) when every expression it contains has its type under its own annotations,
those annotations agree with the types of the variables, and the nondeterministic assignments
write variables of ground types:
* the right-hand side of every deterministic `init` and `set`, and the condition of every
  deterministic `ite`, has the type of its variable or the Boolean type (`Block.rhsTyped`);
* the conditions of the `assume`s, `assert`s and `cover`s, and the deterministic guards and the
  invariants of the loops, are Boolean (`Block.condsTyped`);
* the annotation of every free-variable occurrence is the type of that variable
  (`Block.fvarTypesWellAnnotated`);
* some name set holding the variables the nondeterministic assignments write, and the variables
  assigned copies of them, gives each a ground type where it is assigned (`Block.nondetGround`).

A typing predicate whose typed expressions evaluate, in a store holding at each annotated
free-variable occurrence a value of the annotated type, to a value of their type, forms a
`TypedEval`.

Key definitions: `Block.condsTyped`, `Block.ExprsTyped`, `Block.WellTyped`, `TypedEval`. -/

namespace Imperative

public section

variable {P : PureExpr} [HasBool P]

/-- The condition of an `assume`, `assert` or `cover` has the Boolean type (under the typing
    predicate `Typ`); other commands impose nothing. -/
@[expose] def CmdExt.condsTyped (Typ : P.Expr → P.Ty → Prop) : CmdExt P → Prop
  | .cmd (.assume _ e _) => Typ e HasBool.boolTy
  | .cmd (.assert _ e _) => Typ e HasBool.boolTy
  | .cmd (.cover _ e _) => Typ e HasBool.boolTy
  | _ => True

mutual
/-- **Boolean conditions.**  The conditions of the `assume`s, `assert`s and `cover`s of the
    statement, and the deterministic guards and the invariants of its loops, in nested blocks,
    branches and loop bodies included, have the Boolean type. -/
@[expose] def Stmt.condsTyped (Typ : P.Expr → P.Ty → Prop) : Stmt P (CmdExt P) → Prop
  | .cmd c => CmdExt.condsTyped Typ c
  | .block _ bss _ => Block.condsTyped Typ bss
  | .ite _ tss ess _ => Block.condsTyped Typ tss ∧ Block.condsTyped Typ ess
  | .loop g _ invs body _ => (match g with | .det g => Typ g HasBool.boolTy | .nondet => True) ∧
    (∀ lp ∈ invs, Typ lp.2 HasBool.boolTy) ∧ Block.condsTyped Typ body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `Stmt.condsTyped` of every statement of the list. -/
@[expose] def Block.condsTyped (Typ : P.Expr → P.Ty → Prop) : List (Stmt P (CmdExt P)) → Prop
  | [] => True
  | s :: rest => Stmt.condsTyped Typ s ∧ Block.condsTyped Typ rest
end

variable [HasFvar P] [HasFvars P]

/-- **Typed expressions.**  The expressions of `ss` are typed under the typing predicate `Typ`
    (`Typ e ty`: `e` has the type `ty` under its own annotations) and the typing `Γ` of the names
    in scope at its entry (`Block.rhsTyped`, `Block.condsTyped`), and the annotations of its
    free-variable occurrences agree with `Γ` and the declarations of `ss`
    (`Block.fvarTypesWellAnnotated`). -/
@[expose] def Block.ExprsTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P)
    (ss : List (Stmt P (CmdExt P))) : Prop :=
  Block.rhsTyped Typ Γ ss ∧ Block.condsTyped Typ ss ∧ Block.fvarTypesWellAnnotated Γ ss

/-- **A well-typed statement list**, under the typing `Γ` of the names in scope at its entry,
    for the typing predicate `Typ` and the ground types `Ground`: its expressions are typed
    (`Block.ExprsTyped`), and the values its nondeterministic assignments draw, and the copies
    of them, have ground types (`Block.nondetGround`). -/
@[expose] def Block.WellTyped (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop)
    (Γ : VarTyping P) (ss : List (Stmt P (CmdExt P))) : Prop :=
  Block.ExprsTyped Typ Γ ss ∧ ∃ N, Block.nondetGround Ground N Γ ss

/-- **A typing predicate whose typed expressions evaluate**: an expression typed at `ty`
    evaluates, in a store holding at each annotated free-variable occurrence a value of the
    annotated type, to a value of type `ty`; and the values of the Boolean type are the two
    Boolean values. -/
structure TypedEval (P : PureExpr) [HasFvars P] [HasBool P] where
  /-- `Typ e ty`: `e` has the type `ty` under its own annotations. -/
  Typ : P.Expr → P.Ty → Prop
  /-- A typed expression evaluates to a value of its type. -/
  eval_of_typed : ∀ {F : P.Factory} {σ : SemanticStore P} {e : P.Expr} {ty : P.Ty}, Typ e ty →
    (∀ p ∈ HasFvars.getTypedFvars e, ∃ v, σ p.1 = some v ∧ HasVal.valueOfTy F v p.2) →
    ∃ v, P.eval F σ e = some v ∧ HasVal.valueOfTy F v ty
  /-- The values of the Boolean type are the two Boolean values. -/
  valueOfTy_bool : ∀ {F : P.Factory} {v : P.Val}, HasVal.valueOfTy F v HasBool.boolTy →
    v = HasBool.ttVal F ∨ v = HasBool.ffVal F

end -- public section

end Imperative
