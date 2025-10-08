/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.Scopes

/-! ## State for (Partial) Evaluation of Lambda Expressions

See `Strata.DL.Lambda.LExprEval` for the partial evaluator.
-/

namespace Lambda

open Std (ToFormat Format format)

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier] {ExtraRestrict : Type}
---------------------------------------------------------------------

/-
Configuration for symbolic execution, where we have `gen` for keeping track of
fresh `fvar`'s numbering. We also have a `fuel` argument for the evaluation
function, and support for factory functions.

We rely on the parser disallowing Lambda variables to begin with `$__`, which is
reserved for internal use. Also see `TEnv.genExprVar` used during type inference
and `LState.genVar` used during evaluation.
-/
structure EvalConfig (Identifier : Type) (ExtraRestrict : Type := Empty) where
  factory : @Factory Identifier ExtraRestrict
  fuel : Nat := 200
  varPrefix : String := "$__"
  gen : Nat := 0

instance : ToFormat (EvalConfig Identifier ExtraRestrict) where
  format c :=
    f!"Eval Depth: {(repr c.fuel)}" ++ Format.line ++
    f!"Variable Prefix: {c.varPrefix}" ++ Format.line ++
    f!"Variable gen count: {c.gen}" ++ Format.line ++
    f!"Factory Functions:" ++ Format.line ++
    Std.Format.joinSep c.factory.toList f!"{Format.line}"

def EvalConfig.init : (EvalConfig Identifier ExtraRestrict) :=
  { factory := @Factory.default Identifier ExtraRestrict,
    fuel := 200,
    gen := 0 }

def EvalConfig.incGen (c : (EvalConfig Identifier ExtraRestrict)) : (EvalConfig Identifier ExtraRestrict) :=
    { c with gen := c.gen + 1 }

def EvalConfig.genSym (x : String) (c : (EvalConfig String ExtraRestrict)) : String × (EvalConfig String ExtraRestrict) :=
  let new_idx := c.gen
  let c := c.incGen
  let new_var := c.varPrefix ++ x ++ toString new_idx
  (new_var, c)

---------------------------------------------------------------------

/-- The Lambda evaluation state. -/
structure LState (Identifier : Type) (ExtraRestrict : Type := Empty) where
  config : (EvalConfig Identifier ExtraRestrict)
  state : (Scopes Identifier ExtraRestrict)

-- scoped notation (name := lstate) "Σ" => LState

def LState.init : (LState Identifier ExtraRestrict) :=
  { state := [],
    config := EvalConfig.init }

/-- An empty `LState` -/
instance : EmptyCollection (LState Identifier ExtraRestrict) where
  emptyCollection := LState.init

instance : Inhabited (LState Identifier ExtraRestrict) where
  default := LState.init

instance : ToFormat (LState Identifier ExtraRestrict) where
  format s :=
    let { state, config }  := s
    format f!"State:{Format.line}{state}{Format.line}{Format.line}\
              Evaluation Config:{Format.line}{config}{Format.line}\
              {Format.line}"

/--
Add function `func` to the existing factory of functions in `σ`. Redefinitions
are not allowed.
-/
def LState.addFactoryFunc (σ : LState Identifier ExtraRestrict) (func : (LFunc Identifier ExtraRestrict)) : Except Format (LState Identifier ExtraRestrict) := do
  let F ← σ.config.factory.addFactoryFunc func
  .ok { σ with config := { σ.config with factory := F }}

/--
Append `Factory f` to the existing factory of functions in `σ`, checking for
redefinitions.
-/
def LState.addFactory (σ : (LState Identifier ExtraRestrict)) (F : @Factory Identifier ExtraRestrict) : Except Format (LState Identifier ExtraRestrict) := do
  let oldF := σ.config.factory
  let newF ← oldF.addFactory F
  .ok { σ with config := { σ.config with factory := newF } }

/--
Get all the known variables from the scopes in state `σ`.
-/
def LState.knownVars (σ : (LState Identifier ExtraRestrict)) : List Identifier :=
  go σ.state []
  where go (s : Scopes Identifier ExtraRestrict) (acc : List Identifier) :=
  match s with
  | [] => acc
  | m :: rest => go rest (acc ++ m.keys)

/--
Generate a fresh (internal) identifier with the base name
`x`; i.e., `σ.config.varPrefix ++ x`.
-/
def LState.genVar (x : String) (σ : (LState String ExtraRestrict)) : (String × (LState String ExtraRestrict)) :=
  let (new_var, config) := σ.config.genSym x
  let σ := { σ with config := config }
  let known_vars := LState.knownVars σ
  if new_var ∈ known_vars then
    panic s!"[LState.genVar] Generated variable {new_var} is not fresh!\n\
             Known variables: {σ.knownVars}"
  else
    (new_var, σ)

/--
Generate fresh identifiers, each with the base name in `xs`.
-/
def LState.genVars (xs : List String) (σ : (LState String ExtraRestrict)) : (List String × (LState String ExtraRestrict)) :=
  let (vars, σ') := go xs σ []
  (vars.reverse, σ')
  where go (xs : List String) (σ : LState String ExtraRestrict) (acc : List String) :=
    match xs with
    | [] => (acc, σ)
    | x :: rest =>
      let (x', σ) := LState.genVar x σ
      go rest σ (x' :: acc)

instance : ToFormat (Identifier × LState Identifier ExtraRestrict) where
  format im :=
    f!"New Variable: {im.fst}{Format.line}\
       Gen in EvalConfig: {im.snd.config.gen}{Format.line}\
       {im.snd}"

---------------------------------------------------------------------

/--
Substitute `.fvar`s in `e` by looking up their values in `σ`.
-/
def LExpr.substFvarsFromState (σ : (LState Identifier ExtraRestrict)) (e : (LExpr (LMonoTy ExtraRestrict) Identifier)) : (LExpr (LMonoTy ExtraRestrict) Identifier) :=
  let sm := σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))
  Lambda.LExpr.substFvars e sm

---------------------------------------------------------------------

end Lambda
