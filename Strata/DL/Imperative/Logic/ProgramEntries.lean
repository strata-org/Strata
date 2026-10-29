/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination

/-! # Programs and their entries, for event languages

An event language runs a statement from a configuration. An analysis is about
programs, and a program has entries: the places a run may start, with the
values of the variables there. `ProgramEntries EL` gives the programs, their
entries, and the configuration each entry starts a run from, in one of a family
of event languages `EL i`. Core uses two event languages, one for structured
procedure bodies and one for CFG bodies.

`ProgramEntries.Raises` says that some run of at most `n` steps from an entry
raises a trace, which is what an analysis of safety properties reads.
-/

public section

namespace Strata.Logic

open Imperative

/-- The programs and entries of a family of event languages `EL i`: each entry
    of a program starts a run from a configuration of one of them. -/
structure ProgramEntries {P : PureExpr} {EventT Idx : Type} (EL : Idx → EventLang P EventT) where
  Program : Type
  Entry : Type
  entries : Program → Entry → Prop
  start : Program → Entry → (i : Idx) × (EL i).CfgT

variable {P : PureExpr} {EventT Idx : Type} {EL : Idx → EventLang P EventT}

/-- Some run of at most `n` steps from entry `entry` of `p` raises `trace`. -/
@[expose] def ProgramEntries.Raises (E : ProgramEntries EL) (p : E.Program) (entry : E.Entry)
    (n : Nat) (trace : List EventT) : Prop :=
  ∃ cfg, (EL (E.start p entry).1).ReachesWithin n (E.start p entry).2 trace cfg

end Strata.Logic

end -- public section
