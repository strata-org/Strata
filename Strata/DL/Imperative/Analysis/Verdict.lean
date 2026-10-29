/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.ProgramEntries
public import Strata.DL.Imperative.Logic.TraceInterp

/-! # Per-assertion verdicts of deductive verification

Deductive verification reports one `Verdict` per assertion of a program. A
verdict names an entry of the program, never a configuration, and is a claim
about the runs of event languages `EL i` from the program's entries
(`ProgramEntries`), stated with bounded reachability, so no claim needs
induction or coinduction on the program. Validity of an assertion on a trace is
`Trace.AssertionValid` under a condition interpretation `I`:

- `valid`: from every entry, every trace a run raises has the assertion valid;
- `failed e`: `e` is an entry from which some run raises a trace on which the
  assertion is not valid;
- `unknown e?`: no claim, with the entry the analyzer was looking at, if any.

`VerdictCorrect` gives each verdict its meaning.
-/

public section

namespace Strata.Analysis

open Imperative Strata.Logic

/-- What deductive verification reports about one assertion. `failed` carries
    the entry it is about. `unknown` may carry one too, such as the entry of a
    model the solver returned, and claims nothing about it. -/
inductive Verdict (Entry : Type) where
  | valid
  | failed (entry : Entry)
  | unknown (entry : Option Entry)

variable {P : PureExpr} {Idx : Type} {EL : Idx → EventLang P (Event P)}

/-- What verdict `v` about assertion `a` claims, for the runs from the entries
    of `p`, with conditions read through `I`. -/
@[expose] def VerdictCorrect (I : ConditionInterp P) (E : ProgramEntries EL) (p : E.Program)
    (a : AssertId P) : Verdict E.Entry → Prop
  | .valid => ∀ e, E.entries p e → ∀ n trace,
      E.Raises p e n trace → Trace.AssertionValid P I a trace
  | .failed e => E.entries p e ∧ ∃ n trace,
      E.Raises p e n trace ∧ ¬ Trace.AssertionValid P I a trace
  | .unknown _ => True

/-- Keep a `valid` verdict and turn every other one into `unknown`. This is how
    a report about a transformed program is read back on the original: `failed`
    claims a run of the transformed program, which need not exist in the
    original. -/
@[expose] def Verdict.keepValid {Entry Entry' : Type} : Verdict Entry → Verdict Entry'
  | .valid => .valid
  | _ => .unknown none

/-- `t'` reflects the validity of `t` under `I`: every assertion valid on `t'`
    is valid on `t`. This is what runs of a transformed program must keep for
    deductive verification to carry back to the original. Equality has it, and
    a transformed trace may also carry extra assertions. -/
@[expose] def ValidityReflected (I : ConditionInterp P) (t t' : Trace P) : Prop :=
  ∀ a, Trace.AssertionValid P I a t' → Trace.AssertionValid P I a t

end Strata.Analysis

end -- public section
