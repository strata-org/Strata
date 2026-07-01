/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.Scopes
import all Strata.DL.Lambda.LExpr
import Strata.Util.Name

/-! ## State for (Partial) Evaluation of Lambda Expressions

See `Strata.DL.Lambda.LExprEval` for the partial evaluator.
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

public section

variable {T : LExprParams} [Inhabited T.Metadata] [BEq T.Metadata] [DecidableEq T.IDMeta] [BEq T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat (Scopes T)] [Inhabited (LExpr T.mono)]
---------------------------------------------------------------------

/-
Configuration for symbolic execution, where we have `usedNames` for tracking
which variable names have been generated. We also have a `fuel` argument for
the evaluation function, and support for factory functions.
-/
structure EvalConfig (T : LExprParams) where
  factory : @Factory T
  fuel : Nat := 200
  usedNames : Std.HashSet String := {}

instance : ToFormat (EvalConfig T) where
  format c :=
    f!"Eval Depth: {(repr c.fuel)}" ++ Format.line ++
    f!"Factory Functions:" ++ Format.line ++
    Std.Format.joinSep c.factory.toArray.toList f!"{Format.line}"

def EvalConfig.init : EvalConfig T :=
  { factory := @Factory.default T,
    fuel := 200,
    usedNames := {} }

def EvalConfig.genSym (x : String) (c : EvalConfig T) : String × EvalConfig T :=
  let (base, startSuffix) := Strata.Name.breakDisambiguated x
  let new_var := Strata.Name.findUnique base startSuffix c.usedNames
  let c := { c with usedNames := c.usedNames.insert new_var }
  (new_var, c)

---------------------------------------------------------------------

/-- The Lambda evaluation state. -/
structure LState (T : LExprParams) where
  config : EvalConfig T
  state : Scopes T

-- scoped notation (name := lstate) "Σ" => LState

def LState.init : LState T :=
  { state := [],
    config := EvalConfig.init }

/-- An empty `LState` -/
instance : EmptyCollection (LState T) where
  emptyCollection := LState.init

instance : Inhabited (LState T) where
  default := LState.init

instance : ToFormat (LState T) where
  format s :=
    let { state, config }  := s
    format f!"State:{Format.line}{state}{Format.line}{Format.line}\
              Evaluation Config:{Format.line}{config}{Format.line}\
              {Format.line}"

/--
Add function `func` to the existing factory of functions in `σ`. Redefinitions
are not allowed.
-/
def LState.addFactoryFunc (σ : LState T) (func : (LFunc T)) : Except DiagnosticModel (LState T) := do
  let F ← σ.config.factory.tryPush func
  .ok { σ with config := { σ.config with factory := F }}

/--
Append `Factory f` to the existing factory of functions in `σ`, checking for
redefinitions.
-/
def LState.addFactory (σ : (LState T)) (F : @Factory T) : Except DiagnosticModel (LState T) := do
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
def LState.knownVars (σ : LState T) : List T.Identifier :=
  go σ.state []
  where go (s : Scopes T) (acc : List T.Identifier) :=
  match s with
  | [] => acc
  | m :: rest => go rest (acc ++ m.keys)

/--
Generate a fresh (internal) identifier with the base name
`x`, reusing the bare name when possible and adding `@N` suffixes
only when disambiguation is needed.
-/
def LState.genVar {IDMeta} [Inhabited IDMeta] [DecidableEq IDMeta] (x : String) (σ : LState ⟨Unit, IDMeta⟩) : String × LState ⟨Unit, IDMeta⟩ :=
  let (new_var, config) := σ.config.genSym x
  let σ := { σ with config := config }
  let known_vars := LState.knownVars σ
  let new_var := ⟨ new_var, Inhabited.default  ⟩
  if new_var ∈ known_vars then
    panic s!"[LState.genVar] Generated variable {new_var} is not fresh!\n\
             Known variables: {known_vars}"
  else
    (new_var.name, σ)

/--
Generate fresh identifiers, each with the base name in `xs`.
-/
def LState.genVars (xs : List String) (σ : (LState ⟨Unit, Unit⟩)) : (List String × (LState ⟨Unit, Unit⟩)) :=
  let (vars, σ') := go xs σ []
  (vars.reverse, σ')
  where go (xs : List String) (σ : LState ⟨Unit, Unit⟩) (acc : List String) :=
    match xs with
    | [] => (acc, σ)
    | x :: rest =>
      let (x', σ) := LState.genVar x σ
      go rest σ (x' :: acc)

instance : ToFormat (T.Identifier × LState T) where
  format im :=
    f!"New Variable: {im.fst}{Format.line}\
       {im.snd}"

---------------------------------------------------------------------

/--
A free variable -> expression mapping.
Compatible with `Imperative.SemanticStore` from `Strata.DL.Imperative.CmdSemantics`.
-/
@[expose] def Env (T : LExprParams) := T.Identifier → Option (LExpr T.mono)

instance : CoeFun (Env T) (fun _ => T.Identifier → Option (LExpr T.mono)) where
  coe f := f

def Env.mk (f : T.Identifier → Option (LExpr T.mono)) : Env T := f

def Scopes.toEnv (s : Scopes T) : Env T :=
  Env.mk (fun t => (s.find? t).map (·.snd))

/--
Substitute `.fvar`s in `e` by looking up their values in `env`.
The replacement expressions must be closed (no dangling bvars).
-/
def LExpr.substFvarsFromEnv (env : Env T) (e : LExpr T.mono) : LExpr T.mono :=
  match e with
  | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar _ name _ => match env name with | some to => to | none => e
  | .abs m nm ty e' => .abs m nm ty (substFvarsFromEnv env e')
  | .quant m qk nm ty tr' e' => .quant m qk nm ty (substFvarsFromEnv env tr') (substFvarsFromEnv env e')
  | .app m fn e' => .app m (substFvarsFromEnv env fn) (substFvarsFromEnv env e')
  | .ite m c t e' => .ite m (substFvarsFromEnv env c) (substFvarsFromEnv env t) (substFvarsFromEnv env e')
  | .eq m e1 e2 => .eq m (substFvarsFromEnv env e1) (substFvarsFromEnv env e2)

end -- public section
end Lambda
