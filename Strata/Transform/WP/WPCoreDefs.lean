/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.Passive.Shadow
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.SpecificationProps
public import Strata.Transform.Passive.CoreTyped

/-! # The relations and the precondition of the WP trace over-approximation

The trace relation `LastFailureReflected` (with `refl` and `trans`), the initial-environment
relation `EntryRel`, the target parameters `wpTgtParams` and the syntactic precondition `WPPre`
of the statement that the WP phase over-approximates the traces of a Core statement list.

Key definitions: `LastFailureReflected`, `EntryRel`, `wpTgtParams`, `WPPre`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [HasBool P]

/-- **The last failure is reflected, with its kind and id**: when the trace `t` ends in a
    failing occurrence of a check (an assertion or a cover) with the id `a` (a label and metadata)
    and some condition `e`, every assumption before it evaluating to `true`, then `t'` ends in a
    failing occurrence of a check of the same kind with the same id and some condition `e'`, every
    assumption before it evaluating to `true` (`ClaimK`, whose flag `k` is the kind).  That is: a
    trace ending in an assertion with id `a` whose condition evaluates to `false` is matched by a
    trace ending in an assertion with id `a` whose condition evaluates to `false`, and a trace
    ending in a cover with id `a` whose condition evaluates to `true` is matched by a trace ending
    in a cover with id `a` whose condition evaluates to `true`.  The relation is keyed by kind and
    id, not by condition: a phase may rewrite the conditions of checks. -/
@[expose] def LastFailureReflected (t t' : List (Event P)) : Prop :=
  ∀ (k : Bool) (a : AssertId P) (e : P.Expr), ClaimK k a e t → ∃ e', ClaimK k a e' t'

/-- `LastFailureReflected` is reflexive. -/
theorem LastFailureReflected.refl (t : List (Event P)) : LastFailureReflected t t :=
  fun _ _ e h => ⟨e, h⟩

/-- `LastFailureReflected` is transitive. -/
theorem LastFailureReflected.trans {t t' t'' : List (Event P)} (h₁ : LastFailureReflected t t')
    (h₂ : LastFailureReflected t' t'') : LastFailureReflected t t'' :=
  fun k a e h => (h₁ k a e h).elim fun e' h' => h₂ k a e' h'

end -- public section

end WP
end Imperative

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.Specification
  Imperative.Specification.Transform Core.Logic Strata.Logic

public section

/-- The initial-environment relation of the WP phase with the free-variable types `tys`: equal
    environments whose store gives every variable of `tys` it binds a value of its declared type
    (`TyOK`), and binds no name of the form of a fresh name (`freshName`) that is not a variable
    of `tys`.  WP copies a variable it saves into a fresh `init` of its declared type, and declares
    fresh names that avoid only the variables of `tys`, the identifiers of the list and the
    global names. -/
@[expose] def EntryRel (tys : Tys Expression) (ρ ρ' : Env Expression) : Prop :=
  ρ' = ρ ∧ TyOK ρ.factory tys (tys.map (·.1)) (tys.map (·.1)) ρ.store ∧
    ∀ x, (ρ.store x).isSome → ∀ (b : String) (k : Nat), x = freshName b k → x ∈ tys.map (·.1)

/-- The initial-environment parameters of the output of the WP phase: those of the input
    without reserved prefixes. -/
@[expose] def wpTgtParams (params : InitEnvWFParams) : InitEnvWFParams :=
  { params with prefixIdents := [] }

/-- The syntactic conditions under which the WP phase with the free-variable types `tys`
    over-approximates the statement list `ss`: `ss` reads only variables of `tys`, is well scoped
    from them with its assigned variables as locals (`Block.WellScoped`: no loops, calls or
    nondeterministic guards, each `init` declares a name not in scope, each `set` and each read
    is of a name in scope), and every `exit` of `ss` targets an enclosing block. For
    `tys = p.paramTys` these are what `checkLoopFree p` checks (`checkLoopFree_ok`). -/
@[expose] def WPPre (tys : Tys Expression) (ss : Statements) : Prop :=
  (∀ x ∈ Block.freeVars ss, x ∈ tys.map (·.1)) ∧
    Block.WellScoped (Block.assignedVars ss) (tys.map (·.1)) ss ∧ Block.exitsCoveredByBlocks [] ss

end -- public section

end WP
end Core
