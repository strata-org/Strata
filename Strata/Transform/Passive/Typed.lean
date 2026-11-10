/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.DL.Imperative.CmdCallFormals

/-! # Typed right-hand sides

A program's definitions are *typed* by a typing predicate `Typ` (`Typ e ty`: the expression `e`
has the type `ty`) when the right-hand side of every deterministic `init` has the declared type
of its variable (`Block.initsTyped`).  Before the SSA phase a program also assigns: there the
right-hand side of a deterministic `set` has the type of its variable in the typing of the names
in scope (`Block.rhsTyped`, scoped like the annotation check `Block.fvarTypesWellAnnotated`), and
the condition of a deterministic `ite` is Boolean.

The phases rewrite right-hand sides with the operations of `WPOps`; `TypedLaws` are the laws of
`Typ` they need: a conditional has a type exactly when its condition is Boolean and its branches
have that type, a substitution of expressions having the annotated types of the variables they
replace keeps the type, and the annotation of an
occurrence in a typed expression types a variable annotated with it.

The values a nondeterministic assignment draws, and the copies of them, are of ground types when
some name set holding the variables they are assigned to has ground types where they are assigned
(`Block.nondetGround`).

Key definitions: `Block.initsTyped`, `Block.rhsTyped`, `Block.nondetGround`, `TypedLaws`. -/

namespace Imperative

public section

variable {P : PureExpr}

/-- The right-hand side of a deterministic `init` command has the declared type of its variable
    (under the typing predicate `Typ`); other commands impose nothing. -/
@[expose] def CmdExt.initsTyped (Typ : P.Expr → P.Ty → Prop) : CmdExt P → Prop
  | .cmd (.init _ ty (.det e) _) => Typ e ty
  | _ => True

mutual
/-- Every deterministic `init` of the statement, in nested blocks, branches and loop bodies
    included, has a right-hand side of the declared type of its variable. -/
@[expose] def Stmt.initsTyped (Typ : P.Expr → P.Ty → Prop) : Stmt P (CmdExt P) → Prop
  | .cmd c => CmdExt.initsTyped Typ c
  | .block _ bss _ => Block.initsTyped Typ bss
  | .ite _ tss ess _ => Block.initsTyped Typ tss ∧ Block.initsTyped Typ ess
  | .loop _ _ _ body _ => Block.initsTyped Typ body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `Stmt.initsTyped` of every statement of the list. -/
@[expose] def Block.initsTyped (Typ : P.Expr → P.Ty → Prop) : List (Stmt P (CmdExt P)) → Prop
  | [] => True
  | s :: rest => Stmt.initsTyped Typ s ∧ Block.initsTyped Typ rest
end

/-- The right-hand side of a deterministic `init` has the declared type of its variable, and
    that of a deterministic `set` has the type `Γ` gives its variable (under the typing predicate
    `Typ`); other commands impose nothing. -/
@[expose] def CmdExt.rhsTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P) : CmdExt P → Prop
  | .cmd (.init _ ty (.det e) _) => Typ e ty
  | .cmd (.set x (.det e) _) => ∃ T, Γ x = some T ∧ Typ e T
  | _ => True

/-- `Block.initsTyped` of a concatenation is that of its parts. -/
theorem Block.initsTyped_append {Typ : P.Expr → P.Ty → Prop} :
    ∀ (a b : List (Stmt P (CmdExt P))),
      Block.initsTyped Typ (a ++ b) ↔ Block.initsTyped Typ a ∧ Block.initsTyped Typ b
  | [], _ => by simp [Block.initsTyped]
  | s :: a, b => by simp [Block.initsTyped, Block.initsTyped_append a b, and_assoc]

variable [HasFvar P] [HasFvars P] [HasBool P]

mutual
/-- **Typed right-hand sides.**  Every deterministic `init` and `set` of the statement has a
    right-hand side of the type of its variable: the declared type for an `init`, the type `Γ`
    gives for a `set`, where `Γ` types the names in scope before the statement and each
    definition adds its declared type for the statements after it in its scope (as in
    `Stmt.fvarTypesWellAnnotated`); and the condition of every deterministic `ite` has the
    Boolean type. -/
@[expose] def Stmt.rhsTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P) :
    Stmt P (CmdExt P) → Prop
  | .cmd c => CmdExt.rhsTyped Typ Γ c
  | .block _ bss _ => Block.rhsTyped Typ Γ bss
  | .ite c tss ess _ => (match c with | .det c => Typ c HasBool.boolTy | .nondet => True) ∧
    Block.rhsTyped Typ Γ tss ∧ Block.rhsTyped Typ Γ ess
  | .loop _ _ _ body _ => Block.rhsTyped Typ Γ body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `Stmt.rhsTyped` over a list of statements, each checked with the definitions of the
    statements before it added to `Γ`. -/
@[expose] def Block.rhsTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P) :
    List (Stmt P (CmdExt P)) → Prop
  | [] => True
  | s :: rest =>
    Stmt.rhsTyped Typ Γ s ∧ Block.rhsTyped Typ (Γ.extend (Stmt.typedDefinedVars s)) rest
end

/-- The right-hand side `rhs` of an assignment to a variable passes a value of the name set `N`
    on: it is nondeterministic, or it is a variable of `N`. -/
@[expose] def ExprOrNondet.feeds (N : P.Ident → Prop) : ExprOrNondet P → Prop
  | .nondet => True
  | .det e => ∃ y, HasFvar.getFvar e = some y ∧ N y

/-- The command keeps the name set `N` closed and ground-typed: an `init` or a `set` whose
    right-hand side passes a value of `N` on (`ExprOrNondet.feeds`) assigns a variable of `N`,
    and every variable of `N` an `init` or a `set` assigns has a type satisfying `Ground`: the
    declared type for an `init`, the type `Γ` gives for a `set`. Other commands impose
    nothing. -/
@[expose] def CmdExt.nondetGround (Ground : P.Ty → Prop) (N : P.Ident → Prop)
    (Γ : VarTyping P) : CmdExt P → Prop
  | .cmd (.init x ty rhs _) => (rhs.feeds N → N x) ∧ (N x → Ground ty)
  | .cmd (.set x rhs _) => (rhs.feeds N → N x) ∧ (N x → ∃ T, Γ x = some T ∧ Ground T)
  | _ => True

mutual
/-- **Ground-typed nondeterministic values.**  Every `init` and `set` of the statement, in
    nested blocks, branches and loop bodies included, satisfies `CmdExt.nondetGround` for the
    name set `N`: the variables a nondeterministic assignment writes are in `N`, so are the
    variables assigned a copy of a variable of `N`, and every variable of `N` has a type
    satisfying `Ground` where it is assigned. `Γ` types the names in scope before the statement
    and each definition adds its declared type for the statements after it in its scope (as in
    `Stmt.fvarTypesWellAnnotated`). -/
@[expose] def Stmt.nondetGround (Ground : P.Ty → Prop) (N : P.Ident → Prop) (Γ : VarTyping P) :
    Stmt P (CmdExt P) → Prop
  | .cmd c => CmdExt.nondetGround Ground N Γ c
  | .block _ bss _ => Block.nondetGround Ground N Γ bss
  | .ite _ tss ess _ => Block.nondetGround Ground N Γ tss ∧ Block.nondetGround Ground N Γ ess
  | .loop _ _ _ body _ => Block.nondetGround Ground N Γ body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- `Stmt.nondetGround` over a list of statements, each checked with the definitions of the
    statements before it added to `Γ`. -/
@[expose] def Block.nondetGround (Ground : P.Ty → Prop) (N : P.Ident → Prop) (Γ : VarTyping P) :
    List (Stmt P (CmdExt P)) → Prop
  | [] => True
  | s :: rest =>
    Stmt.nondetGround Ground N Γ s ∧
      Block.nondetGround Ground N (Γ.extend (Stmt.typedDefinedVars s)) rest
end

end -- public section

namespace WP

public section

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBool P] [WPOps P]

/-- **The laws of a typing predicate** `Typ` that the phases rewriting right-hand sides need:
    a conditional has a type exactly when its condition has the
    Boolean type and both branches have that type, and its annotated free-variable occurrences
    include those of its parts; substituting, for the substituted variables,
    expressions having the types their annotated occurrences carry keeps the type;
    and the annotation of a
    free-variable occurrence of a typed expression types every variable annotated with it. -/
structure TypedLaws (Typ : P.Expr → P.Ty → Prop) : Prop where
  /-- The type of a conditional. -/
  ite : ∀ {c t f : P.Expr} {ty : P.Ty},
    Typ (WPOps.ite c t f) ty ↔ Typ c HasBool.boolTy ∧ Typ t ty ∧ Typ f ty
  /-- A substitution of expressions of the annotated types keeps the type. -/
  substFn : ∀ {e : P.Expr} {ty : P.Ty} (g : P.Ident → Option P.Expr), Typ e ty →
    (∀ p ∈ HasFvars.getTypedFvars e, ∀ v, g p.1 = some v → Typ v p.2) →
    Typ (WPOps.substFn e g) ty
  /-- An annotated free-variable occurrence of a part of a conditional is one of the
      conditional's. -/
  typedFvars_ite : ∀ {c t f : P.Expr} {p : P.Ident × P.Ty},
    (p ∈ HasFvars.getTypedFvars c ∨ p ∈ HasFvars.getTypedFvars t ∨
      p ∈ HasFvars.getTypedFvars f) → p ∈ HasFvars.getTypedFvars (WPOps.ite c t f)
  /-- A typed variable carries its type as its annotation. -/
  getFvar : ∀ {e : P.Expr} {ty : P.Ty} {y : P.Ident}, HasFvar.getFvar e = some y → Typ e ty →
    (y, ty) ∈ HasFvars.getTypedFvars e
  /-- A variable annotated with the annotation of an occurrence in a typed expression has the
      annotated type. -/
  var : ∀ {e : P.Expr} {ty : P.Ty} {p : P.Ident × P.Ty} (y : P.Ident), Typ e ty →
    p ∈ HasFvars.getTypedFvars e → Typ (HasFvar.mkVar y (some p.2)) p.2

end -- public section

end WP
end Imperative
