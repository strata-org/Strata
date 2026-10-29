/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination

/-! # Temporal operators over event-language runs

Branching-time temporal operators, as in CTL, over the runs of an `EventLang`.
Each turns a predicate on configurations into one, by quantifying over the runs
from a configuration: over all runs or some run, and over every point of a run
or some point.

| Operator             | CTL | Meaning                                         |
|----------------------|-----|-------------------------------------------------|
| `AllNext`            | AX  | every successor satisfies `S`                   |
| `SomeNext`           | EX  | some successor satisfies `S`                    |
| `AllPathsAlways`     | AG  | every reachable configuration satisfies `S`     |
| `SomePathEventually` | EF  | some reachable configuration satisfies `S`      |
| `AllPathsEventually` | AF  | every run reaches a configuration satisfying `S`|
| `SomePathAlways`     | EG  | some infinite run stays in `S`                  |

`EveryStep` and `SomeStep` read the events a step emits rather than the
configuration it reaches, and `TracesSatisfy` the whole trace of every finite
run, as a safety property does.

`AllPathsEventually` is inductive, so every run must actually reach the target:
a run that diverges or gets stuck first does not satisfy it. `SomePathAlways`
asks for a diverging sequence `ℕ → CfgT` that stays in `S`. `TemporalProps`
relates them to each other and to `MustTerminate`.
-/

public section

namespace Strata.Logic

open Imperative

variable {P : PureExpr} {EventT : Type}

/-- `cfg'` is reachable from `cfg` in zero or more steps. -/
@[expose] def EventLang.Reaches (EL : EventLang P EventT) (cfg cfg' : EL.CfgT) : Prop :=
  ∃ trace, EL.traceStar cfg trace cfg'

/-- Every step from `cfg` emits events `φ` accepts. -/
@[expose] def EventLang.EveryStep (EL : EventLang P EventT) (φ : List EventT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∀ emitted cfg', EL.step cfg emitted cfg' → φ emitted

/-- Some step from `cfg` emits events `φ` accepts. -/
@[expose] def EventLang.SomeStep (EL : EventLang P EventT) (φ : List EventT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∃ emitted cfg', EL.step cfg emitted cfg' ∧ φ emitted

/-- Every successor of `cfg` satisfies `S`. -/
@[expose] def EventLang.AllNext (EL : EventLang P EventT) (S : EL.CfgT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∀ emitted cfg', EL.step cfg emitted cfg' → S cfg'

/-- Some successor of `cfg` satisfies `S`. -/
@[expose] def EventLang.SomeNext (EL : EventLang P EventT) (S : EL.CfgT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∃ emitted cfg', EL.step cfg emitted cfg' ∧ S cfg'

/-- Every configuration reachable from `cfg` satisfies `S`. -/
@[expose] def EventLang.AllPathsAlways (EL : EventLang P EventT) (S : EL.CfgT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∀ cfg', EL.Reaches cfg cfg' → S cfg'

/-- Some configuration reachable from `cfg` satisfies `S`. -/
@[expose] def EventLang.SomePathEventually (EL : EventLang P EventT) (S : EL.CfgT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∃ cfg', EL.Reaches cfg cfg' ∧ S cfg'

/-- Every run from `cfg` reaches a configuration satisfying `S`: `cfg` satisfies
    it, or `cfg` can step and every successor reaches one. -/
inductive EventLang.AllPathsEventually (EL : EventLang P EventT) (S : EL.CfgT → Prop) :
    EL.CfgT → Prop where
  | now {cfg : EL.CfgT} : S cfg → EventLang.AllPathsEventually EL S cfg
  | step {cfg : EL.CfgT}
      (progress : ∃ emitted cfg', EL.step cfg emitted cfg')
      (successors : ∀ emitted cfg', EL.step cfg emitted cfg' →
        EventLang.AllPathsEventually EL S cfg') :
      EventLang.AllPathsEventually EL S cfg

/-- Some diverging sequence from `cfg` stays in configurations satisfying `S`. -/
@[expose] def EventLang.SomePathAlways (EL : EventLang P EventT) (S : EL.CfgT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∃ f : EL.Transitions, f 0 = cfg ∧ EL.Diverges f ∧ ∀ i, S (f i)

/-- Every finite trace of a run from `cfg` satisfies `φ`. -/
@[expose] def EventLang.TracesSatisfy (EL : EventLang P EventT) (φ : List EventT → Prop)
    (cfg : EL.CfgT) : Prop :=
  ∀ trace c, EL.traceStar cfg trace c → φ trace

end Strata.Logic

end -- public section
