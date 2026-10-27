/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StoreRelations
public import Strata.Util.ListUtils

/-! # Imperative command traces

Defines captured assertion, assumption, and cover events and chronological
traces, together with the event-level environment-extension relations built
directly on them.  Condition interpretation, deductive validity, cover
satisfiability, feasibility, and neutrality live in
`Strata.DL.Imperative.Logic.TraceInterp`.

`SemanticStore` and `StoreExtendsWith` are defined in
`Strata.DL.Imperative.StoreRelations`, which this module publicly imports.
Command evaluation builds on this module rather than the reverse, avoiding an
import cycle.
-/

---------------------------------------------------------------------

namespace Imperative

public section

/-! ### Event traces

`assert`, `assume`, and `cover` observations capture the condition together
with the factory and store in which it was encountered. Keeping this snapshot
in the event makes later interpretation independent of subsequent assignments,
scoping, and factory extension.
-/

/-- An argument captured by an event together with the semantic state in which
it was observed. Labels and metadata are retained for assertion identity and
diagnostics; condition interpretation depends only on `factory`, `store`, and
`expr`. -/
structure EventArg (P : PureExpr) where
  /-- Expression factory active when the event was emitted. -/
  factory : P.Factory
  /-- Variable store observed when the event was emitted. -/
  store : SemanticStore P
  /-- Source-level label identifying the observed command. -/
  label : String
  /-- Unevaluated condition captured by the event. -/
  expr : P.Expr
  /-- Source and analysis metadata attached to the command. -/
  metadata : MetaData P

/-- Observable events emitted by Imperative commands. -/
inductive Event (P : PureExpr) where
  /-- An assertion condition that must hold under preceding assumptions. -/
  | assert : EventArg P → Event P
  /-- An assumption condition that constrains later observations. -/
  | assume : EventArg P → Event P
  /-- A coverage condition whose matching occurrence may be checked for
  satisfiability. -/
  | cover : EventArg P → Event P

/-- An Imperative event trace is a chronological list of assertion and
assumption observations. -/
abbrev Trace (P : PureExpr) := List (Event P)

/-! ### Event environment-extension relations

These compare captured events under store extension.  They are phrased directly
over `StoreExtendsWith` (from `StoreRelations`) and so belong with the events
themselves; their property proofs live in
`Strata.DL.Imperative.Logic.TraceRelationsProps`.
-/

/-- Return the condition snapshot carried by an event. -/
@[expose] def Event.condition {P : PureExpr} : Event P → EventArg P
  | .assert condition | .assume condition | .cover condition => condition

/-- An event may stutter when it is an assumption or assertion whose captured
condition evaluates to true. Covers remain observable even when their condition
is true. -/
@[expose] def Event.isTrueAssumeOrAssert {P : PureExpr} [HasBool P] :
    Event P → Prop
  | .assume condition | .assert condition =>
      P.eval condition.factory condition.store condition.expr = some HasBool.tt
  | .cover _ => False

/-- A target event argument extends a source event argument when all observable
fields are unchanged and its target-only register bindings satisfy `Extra`. -/
@[expose] def EventArg.ExtendsEnv {P : PureExpr} (Extra : P.Ident → Prop)
    (source target : EventArg P) : Prop :=
  source.factory = target.factory ∧
  StoreExtendsWith Extra source.store target.store ∧
  source.label = target.label ∧
  source.expr = target.expr ∧
  source.metadata = target.metadata

/-- Events correspond under environment extension when they have the same kind
and their captured arguments correspond under `EventArg.ExtendsEnv`. -/
@[expose] def Event.ExtendsEnv {P : PureExpr} (Extra : P.Ident → Prop) :
    Event P → Event P → Prop
  | .assert source, .assert target => source.ExtendsEnv Extra target
  | .assume source, .assume target => source.ExtendsEnv Extra target
  | .cover source, .cover target => source.ExtendsEnv Extra target
  | _, _ => False

end -- public section
end Imperative
