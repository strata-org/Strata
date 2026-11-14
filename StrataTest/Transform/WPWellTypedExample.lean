/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreTyped
public import Strata.Transform.Passive.Program
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.Identifiers
import all Strata.Languages.Core.Identifiers
meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

/-! # The typing premise of the WP phase holds of a type-checked procedure

The over-approximation theorems of the WP phase (`Core.WP.wpLoopFree_runsOverapproximate`) take
the premise `Core.Statements.WellTyped` of the contract-wrapped body of a procedure, under the
types of its parameters. This file proves that premise for one procedure, `inc`, in the form
`Core.typeCheck` returns it: a check confirms that type checking the parsed program gives that
procedure, up to metadata, and `inc_wellTyped` proves the premise by the typing rules. -/

namespace WPWellTypedExample

open Core Lambda Imperative Imperative.WP

public section

/-- A Core identifier. -/
def id' (name : String) : CoreIdent := ⟨name, ()⟩
/-- An integer variable, annotated with its type. -/
def iv (x : String) : Expression.Expr := .fvar Core.valueLoc (id' x) (some .int)
/-- A binary integer operator with the result type `τ`. -/
def binOp (name : String) (τ : LMonoTy) (a b : Expression.Expr) : Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc (.op Core.valueLoc (id' name) (some (.arrow .int (.arrow .int τ)))) a) b

/-- The precondition of `inc`. -/
def incPre : Expression.Expr := binOp "Int.Gt" .bool (iv "x") (.intConst Core.valueLoc 0)
/-- The postcondition of `inc`. -/
def incPost : Expression.Expr := binOp "Int.Gt" .bool (iv "y") (iv "x")
/-- The body of `inc`. -/
def incBody : Statements :=
  [.cmd (.cmd (.set (id' "y") (.det (binOp "Int.Add" .int (iv "x") (.intConst Core.valueLoc 1))) #[]))]

/-- The procedure `inc` as `Core.typeCheck` returns it, with empty metadata. -/
def inc : Procedure where
  header := { name := id' "inc", typeArgs := [], inputs := [(id' "x", LMonoTy.int)],
              outputs := [(id' "y", LMonoTy.int)] }
  spec := { preconditions := [("pos", ⟨incPre, .Default, #[]⟩)],
            postconditions := [("grows", ⟨incPost, .Default, #[]⟩)] }
  body := .structured incBody

/-- An expression whose free-variable occurrences are annotated with `int` is typed at a ground
    type `τ` when the type checker of annotated expressions gives it the type `τ`. -/
theorem typed {e : Expression.Expr} {τ : LMonoTy} (hτ : τ.IsGround)
    (ha : ∀ p ∈ LExpr.freeVars e, p.2 = some .int) (h : LExpr.typeCheck [] e = some τ) :
    Expression.Typed e (.forAll [] τ) :=
  ⟨τ, by simp [LTy.toMonoType?], hτ, fun _ _ hx => ⟨_, ha _ hx, rfl⟩,
    LExpr.typeCheck_to_HasTypeA h⟩

/-- A typing annotates a list of occurrences when it gives each occurrence its type, a
    decidable condition on a concrete list. -/
theorem annotates_of {Γ : VarTyping Expression} {occs : List (Expression.Ident × Expression.Ty)}
    (h : ∀ p ∈ occs, Γ p.1 = some p.2) : Γ.annotates occs := fun x ty hm => h (x, ty) hm

/-- **The typing premise holds of `inc`**: its contract-wrapped body is well typed under the
    types of its parameters, the premise `htyp` of `wpLoopFree_runsOverapproximate`. -/
theorem inc_wellTyped :
    Statements.WellTyped (fun x => Tys.get? inc.paramTys x) (inc.contractWrapped incBody) := by
  simp only [inc, incBody, Procedure.contractWrapped, List.map, Statements.WellTyped,
    Block.WellTyped, Block.ExprsTyped, Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated,
    HasPassiveCmds.assume, HasPassiveCmds.assert, List.cons_append, List.nil_append]
  refine ⟨⟨⟨⟨⟩, ⟨_, by decide, typed rfl (by decide) rfl⟩, ⟨⟩, ⟨⟩⟩,
    ⟨typed rfl (by decide) rfl, ⟨⟩, typed rfl (by decide) rfl, ⟨⟩⟩, ?_⟩, fun _ => False, ?_⟩
  · repeat' apply And.intro
    all_goals first | trivial | exact annotates_of (by decide)
  · simp [Block.nondetGround, Stmt.nondetGround, CmdExt.nondetGround, ExprOrNondet.feeds]

/--
info: 'WPWellTypedExample.inc_wellTyped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inc_wellTyped

end -- public section

/-! ## `inc` is the procedure type checking returns -/

/-- The program declaring `inc`. -/
private meta def incPgm : StrataDDM.Program :=
#strata
program Core;
procedure inc(x : int, out y : int)
spec {
  requires [pos]: int.gt(x, 0);
  ensures [grows]: int.gt(y, x);
}
{
  y := int.add(x, 1);
};
#end

/-- The first procedure of the type-checked program `incPgm`. -/
private meta def checked : Option Procedure :=
  match Core.typeCheck .quiet (Strata.TransM.run default (Strata.translateProgram incPgm)).fst with
  | .ok p => p.decls.findSome? fun | .proc q _ => some q | _ => none
  | .error _ => none

/-- `p` with empty metadata on its contract checks and its body's assignments. -/
private meta def eraseMd (p : Procedure) : Procedure :=
  let ck := fun ((l, c) : String × Procedure.Check) =>
    (l, { c with expr := Core.eraseLocs c.expr, md := #[] })
  { p with
    spec := { preconditions := p.spec.preconditions.map ck,
              postconditions := p.spec.postconditions.map ck }
    body := match p.body with
      | .structured ss => .structured (ss.map fun
        | .cmd (.cmd (.set x (.det e) _)) => .cmd (.cmd (.set x (.det (Core.eraseLocs e)) #[]))
        | s => s)
      | b => b }

-- Type checking the parsed program gives `inc`, up to metadata.
#guard checked.map eraseMd == some inc

end WPWellTypedExample
