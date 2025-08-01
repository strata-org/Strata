/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.Scopes

namespace Lambda

open Std (ToFormat Format format)

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier]
---------------------------------------------------------------------

/-! ## State for (partial) evaluation of Lambda expressions. -/

/-
Configuration for symbolic execution, where we have `gen` for keeping track of
fresh `fvar`'s numbering. We also have a `fuel` argument for the evaluation
function, and support for factory functions.

We rely on the parser disallowing Lambda variables to begin with `$__`, which is
reserved for internal use. Also see `TEnv.genExprVar` used during type inference
and `LState.genVar` used during evaluation.
-/
structure EvalConfig (Identifier : Type) where
  factory : @Factory Identifier
  fuel : Nat := 200
  varPrefix : String := "$__"
  gen : Nat := 0

instance : ToFormat (EvalConfig Identifier) where
  format c :=
    f!"Eval Depth: {(repr c.fuel)}" ++ Format.line ++
    f!"Variable Prefix: {c.varPrefix}" ++ Format.line ++
    f!"Variable gen count: {c.gen}" ++ Format.line ++
    f!"Factory Functions:" ++ Format.line ++
    Std.Format.joinSep c.factory.toList f!"{Format.line}"

def EvalConfig.init : (EvalConfig Identifier) :=
  { factory := @Factory.default Identifier,
    fuel := 200,
    gen := 0 }

def EvalConfig.incGen (c : (EvalConfig Identifier)) : (EvalConfig Identifier) :=
    { c with gen := c.gen + 1 }

def EvalConfig.genSym (x : String) (c : (EvalConfig String)) : String × (EvalConfig String) :=
  let new_idx := c.gen
  let c := c.incGen
  let new_var := c.varPrefix ++ x ++ toString new_idx
  (new_var, c)

---------------------------------------------------------------------

/-- The Lambda evaluation state. -/
structure LState (Identifier : Type) where
  config : (EvalConfig Identifier)
  state : (Scopes Identifier)

-- scoped notation (name := lstate) "Σ" => LState

def LState.init : (LState Identifier) :=
  { state := [],
    config := EvalConfig.init }

/-- An empty `LState` -/
instance : EmptyCollection (LState Identifier) where
  emptyCollection := LState.init

instance : Inhabited (LState Identifier) where
  default := LState.init

instance : ToFormat (LState Identifier) where
  format s :=
    let { state, config }  := s
    format f!"State:{Format.line}{state}{Format.line}{Format.line}\
              Evaluation Config:{Format.line}{config}{Format.line}\
              {Format.line}"

/--
Add function `func` to the existing factory of functions in `σ`. Redefinitions
are not allowed.
-/
def LState.addFactoryFunc (σ : LState Identifier) (func : (LFunc Identifier)) : Except Format (LState Identifier) := do
  let F ← σ.config.factory.addFactoryFunc func
  .ok { σ with config := { σ.config with factory := F }}

/--
Append `Factory f` to the existing factory of functions in `σ`, checking for
redefinitions.
-/
def LState.addFactory (σ : (LState Identifier)) (F : @Factory Identifier) : Except Format (LState Identifier) := do
  let oldF := σ.config.factory
  let newF ← oldF.addFactory F
  .ok { σ with config := { σ.config with factory := newF } }

/--
Get all the known variables from the scopes in state `σ`.
-/
def LState.knownVars (σ : (LState Identifier)) : List Identifier :=
  go σ.state
  where go (s : Scopes Identifier) :=
  match s with
  | [] => []
  | m :: rest => m.keys ++ go rest

/--
Generate a fresh (internal) identifier with the base name
`x`; i.e., `σ.config.varPrefix ++ x`.
-/
def LState.genVar (x : String) (σ : (LState String)) : (String × (LState String)) :=
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
def LState.genVars (xs : List String) (σ : (LState String)) : (List String × (LState String)) :=
  match xs with
  | [] => ([], σ)
  | x :: rest =>
    let (x', σ) := LState.genVar x σ
    let (xrest', σ) := LState.genVars rest σ
    (x' :: xrest', σ)

instance : ToFormat (Identifier × LState Identifier) where
  format im :=
    f!"New Variable: {im.fst}{Format.line}\
       Gen in EvalConfig: {im.snd.config.gen}{Format.line}\
       {im.snd}"

---------------------------------------------------------------------

/--
Substitute `.fvar`s in `e` by looking up their values in `σ`.
-/
def LExpr.substFvarsFromState (σ : (LState Identifier)) (e : (LExpr Identifier)) : (LExpr Identifier) :=
  let sm := σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))
  Lambda.LExpr.substFvars e sm

---------------------------------------------------------------------

end Lambda
