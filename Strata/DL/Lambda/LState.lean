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

variable {IDMeta : Type} [DecidableEq IDMeta]
---------------------------------------------------------------------

/-
Configuration for symbolic execution, where we have `gen` for keeping track of
fresh `fvar`'s numbering. We also have a `fuel` argument for the evaluation
function, and support for factory functions.

We rely on the parser disallowing Lambda variables to begin with `$__`, which is
reserved for internal use. Also see `TEnv.genExprVar` used during type inference
and `LState.genVar` used during evaluation.
-/
structure EvalConfig (IDMeta : Type) where
  factory : @Factory IDMeta
  fuel : Nat := 200
  varPrefix : String := "$__"
  gen : Nat := 0

instance : ToFormat (EvalConfig IDMeta) where
  format c :=
    f!"Eval Depth: {(repr c.fuel)}" ++ Format.line ++
    f!"Variable Prefix: {c.varPrefix}" ++ Format.line ++
    f!"Variable gen count: {c.gen}" ++ Format.line ++
    f!"Factory Functions:" ++ Format.line ++
    Std.Format.joinSep c.factory.toList f!"{Format.line}"

def EvalConfig.init : (EvalConfig IDMeta) :=
  { factory := @Factory.default IDMeta,
    fuel := 200,
    gen := 0 }

def EvalConfig.incGen (c : (EvalConfig IDMeta)) : (EvalConfig IDMeta) :=
    { c with gen := c.gen + 1 }

def EvalConfig.genSym (x : String) (c : (EvalConfig IDMeta))
    : String × (EvalConfig IDMeta) :=
  let new_idx := c.gen
  let c := c.incGen
  let new_var := c.varPrefix ++ x ++ toString new_idx
  (new_var, c)

---------------------------------------------------------------------

/-- The Lambda evaluation state. -/
structure LState (IDMeta : Type) where
  config : (EvalConfig IDMeta)
  state : (Scopes IDMeta)

-- scoped notation (name := lstate) "Σ" => LState

def LState.init : (LState IDMeta) :=
  { state := [],
    config := EvalConfig.init }

/-- An empty `LState` -/
instance : EmptyCollection (LState IDMeta) where
  emptyCollection := LState.init

instance : Inhabited (LState IDMeta) where
  default := LState.init

instance : ToFormat (LState IDMeta) where
  format s :=
    let { state, config }  := s
    format f!"State:{Format.line}{state}{Format.line}{Format.line}\
              Evaluation Config:{Format.line}{config}{Format.line}\
              {Format.line}"

/--
Add function `func` to the existing factory of functions in `σ`. Redefinitions
are not allowed.
-/
def LState.addFactoryFunc (σ : LState IDMeta) (func : (LFunc IDMeta)) : Except Format (LState IDMeta) := do
  let F ← σ.config.factory.addFactoryFunc func
  .ok { σ with config := { σ.config with factory := F }}

/--
Append `Factory f` to the existing factory of functions in `σ`, checking for
redefinitions.
-/
def LState.addFactory (σ : (LState IDMeta)) (F : @Factory IDMeta) : Except Format (LState IDMeta) := do
  let oldF := σ.config.factory
  let newF ← oldF.addFactory F
  .ok { σ with config := { σ.config with factory := newF } }

/--
Replace the `factory` field of σ with F.
-/
def LState.setFactory (σ : (LState IDMeta)) (F : @Factory IDMeta)
    : (LState IDMeta) :=
  { σ with config := { σ.config with factory := F } }

/--
Get all the known variables from the scopes in state `σ`.
-/
def LState.knownVars (σ : (LState IDMeta)) : List (Identifier IDMeta) :=
  go σ.state []
  where go (s : Scopes IDMeta) (acc : List (Identifier IDMeta)) :=
  match s with
  | [] => acc
  | m :: rest => go rest (acc ++ m.keys)

/--
Generate a fresh (internal) identifier with the base name
`x`; i.e., `σ.config.varPrefix ++ x`.
-/
def LState.genVar {IDMeta} [Inhabited IDMeta] [DecidableEq IDMeta]
    (x : String) (σ : (LState IDMeta))
    : (String × (LState IDMeta)) :=
  let (new_var, config) := σ.config.genSym x
  let σ := { σ with config := config }
  let known_vars := LState.knownVars σ
  let new_var := ⟨ new_var, Inhabited.default⟩
  if new_var ∈ known_vars then
    panic s!"[LState.genVar] Generated variable {new_var} is not fresh!\n\
             Known variables: {σ.knownVars}"
  else
    (new_var.name, σ)

/--
Generate fresh identifiers, each with the base name in `xs`.
-/
def LState.genVars (xs : List String) (σ : (LState Unit)) : (List String × (LState Unit)) :=
  let (vars, σ') := go xs σ []
  (vars.reverse, σ')
  where go (xs : List String) (σ : LState Unit) (acc : List String) :=
    match xs with
    | [] => (acc, σ)
    | x :: rest =>
      let (x', σ) := LState.genVar x σ
      go rest σ (x' :: acc)

instance : ToFormat (Identifier IDMeta × LState IDMeta) where
  format im :=
    f!"New Variable: {im.fst}{Format.line}\
       Gen in EvalConfig: {im.snd.config.gen}{Format.line}\
       {im.snd}"

---------------------------------------------------------------------

/--
Substitute `.fvar`s in `e` by looking up their values in `σ`.
-/
def LExpr.substFvarsFromState (σ : (LState IDMeta)) (e : (LExpr LMonoTy IDMeta)) : (LExpr LMonoTy IDMeta) :=
  let sm := σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))
  Lambda.LExpr.substFvars e sm

---------------------------------------------------------------------

end Lambda
