/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.Util.ListUtils

/-! # Imperative command traces

Defines captured assertion, assumption, and cover events and chronological traces.
Condition interpretation, deductive validity, cover satisfiability, feasibility,
and neutrality live in `Strata.DL.Imperative.Logic.TraceInterp`.
`SemanticStore` lives here because captured events depend on store snapshots;
command evaluation builds on this module rather than the reverse, avoiding an
import cycle.
-/

---------------------------------------------------------------------

namespace Imperative

public section

section

variable (P : PureExpr)

/-
These are intended to be as generic as possible, not using any specific
data structure. They'll probably usually be instantiated with map
lookups.
-/
abbrev SemanticStore := P.Ident → Option P.Expr

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

end

end -- public section
end Imperative
