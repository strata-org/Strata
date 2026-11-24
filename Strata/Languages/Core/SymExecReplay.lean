/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PathExplorer
public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterEval
public import Strata.Languages.Core.InterpreterCFG

/-! # Checking a per-path counterexample by replay

A solver model for a per-path obligation gives values to the path's symbols. Binding each
formal to its symbol's value, and feeding the values of the symbols `x := *` created on the path
as the oracle, gives a concrete start configuration and oracle for `ReplayM`, the replay
monad. Replay runs with assumptions enforced (`enforceInterrupt`) and targets the obligation's
check, identified by label and metadata. The verdict is

* `genuine` if the run reaches the check and the check fails;
* `spurious` if the run reaches the check and the check passes;
* `cantValidate` if replay cannot decide (for example, the model violates an assumption).

The replayed run is a run of the procedure as the symbolic run executed it: for a structured
body, `r.stmts` (`runCoreInterp`); for a CFG body, the CFG `r.graph` from its entry block
(`runCoreInterpCFG`).

A symbol the model leaves out gets its type's default value (`defaultValueIn`): any value is
consistent with a model that does not constrain it.

A merged path stands for several runs, and a model picks one of them: the one that takes, at
each merge, the branch the merge's guard gives under the model. The path's record of choices
(`Obl.choices`) keeps each merge's guard and both branches' symbols, so the oracle of that run
is rebuilt from it (`oracleFor`): a merge contributes the symbols of the branch its guard picks,
the guard evaluated by the concrete evaluator (`evalBounded`) over the model's values. A path
with no merges, or whose merged branches made no choices, keeps a plain list of symbols.
-/

namespace Core.SymExec

open Imperative Lambda

@[expose] public section

/-- The model's value for a symbol, else its type's default; `none` if `sym` is not a
    type-annotated free variable or the type has no default. A join symbol
    (`isJoinValueName`), which names a merged value, gets no default: its value is fixed by its
    definition, so a model without it cannot decide a guard that mentions it, and replay then
    cannot validate the model. -/
def modelValue (F : Lambda.Factory CoreLParams) (model : CoreIdent → Option Expression.Expr)
    (sym : Expression.Expr) : Option Expression.Expr :=
  match sym with
  | .fvar _ x (some ty) =>
    (model x).orElse fun _ => if isJoinValueName x.name then none else defaultValueIn F ty
  | _ => none

/-- The oracle of the run that a record of choices (`ms`, oldest first) stands for: each
    symbol's value (`val`), and at each merge the values of the branch its guard picks
    (`pick`). `none` if a value is missing or a guard does not decide. -/
def oracleFor (pick : Expression.Expr → Option Bool)
    (val : Expression.Expr → Option Expression.Expr) : List Choice → Option (List Expression.Expr)
  | [] => some []
  | .sym x :: rest => do
    let v ← val x
    return v :: (← oracleFor pick val rest)
  | .merge g t e :: rest => do
    let vs ← if (← pick g) then oracleFor pick val t else oracleFor pick val e
    return vs ++ (← oracleFor pick val rest)

/-- The value of a merge guard `g` under a model: `g`'s symbols get their model values
    (`modelValue`) and the concrete evaluator (`evalBounded`, at `fuel`) evaluates it; `none`
    unless the result is a Boolean literal. -/
def guardUnder (F : Lambda.Factory CoreLParams) (model : CoreIdent → Option Expression.Expr)
    (fuel : Nat) (g : Expression.Expr) : Option Bool :=
  let vars := LExpr.freeVars g
  let σ : RStore Expression := fun y =>
    (vars.find? (·.1 == y)).bind fun (y, ty) => modelValue F model (.fvar symExecLoc y ty)
  match evalBounded fuel F σ g with
  | some (.boolConst _ b) => some b
  | _ => none

/-- Replay a model of obligation `o` of run `r` (of a procedure, under the run-time factory
    `F`), through the statements or the CFG the run executed. The oracle is the one of the run
    the model picks (`oracleFor`). `none` if a symbol has neither a model value nor a default,
    or a merge guard on the path does not evaluate to a Boolean under the model
    (`guardUnder`). The check is identified by its label and metadata.

    A merge guard can mention a join symbol (`isJoinValueName`), the name of a value merged at
    an earlier join, and `model` must give it: a model without it gets `none`. A solver's model
    gives every join symbol a value, but the verifier's output program declares join symbols by
    `init`s, whose values it does not ask the solver for (`Core.SMT.isReportedName`), so a caller
    replaying a solver's model must ask for them as well. -/
def replayObl (F : Lambda.Factory CoreLParams) (r : Result) (o : Obl)
    (model : CoreIdent → Option Expression.Expr) (fuel : Nat := 10000) :
    Option (CEValidationVerdict StopReason) := do
  let vals ← r.entry.mapM fun (x, sym) => (modelValue F model sym).map (x, ·)
  let σ : RStore Expression := fun y => (vals.find? (·.1 == y)).map (·.2)
  let oracle ← oracleFor (guardUnder F model fuel) (modelValue F model) o.choices.reverse
  let env : IEnv Expression := { store := .ofStore σ, factory := F }
  let target : AssertId Expression := { label := o.label, md := o.md }
  let config : ReplayCfg Expression :=
    { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
  match r.graph with
  | none =>
    let cfg : IConfig Expression Command := .stmts r.stmts env
    some (runReplay (runCoreInterp (m := ReplayM Expression) (fun _ => none) fuel cfg)
      config (assertFailureHalt target fuel) oracle).1
  | some g =>
    let cfg : ICFGConfig String Command Expression := .atBlock g g.entry env
    -- `runReplay` reads whether the run failed the target check or stopped, not the
    -- configuration it ended in, so the CFG run's final environment stands in for it.
    let run : ReplayM Expression (IConfig Expression Command) :=
      (fun c => .terminal c.env) <$>
        runCoreInterpCFG (m := ReplayM Expression) (fun _ => none) fuel cfg
    some (runReplay run config (assertFailureHalt target fuel) oracle).1

end -- public section

end Core.SymExec
