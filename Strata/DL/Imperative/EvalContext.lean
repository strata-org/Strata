/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.EvalError
public import Strata.DL.Imperative.MetaData
public import Strata.DL.Util.ListMap
public import Strata.DL.Util.Maps

namespace Imperative
open Std (ToFormat Format format)

public section

---------------------------------------------------------------------

/-- An entry in a path condition list. Restricts what can appear as a path
    condition to assumptions and variable declarations. -/
inductive PathConditionEntry (P : PureExpr) where
  /-- An assumption with a label and a boolean expression. -/
  | assumption (label : String) (expr : P.Expr)
  /-- A variable declaration with a name, type, and optional initializer. -/
  | varDecl (name : P.Ident) (ty : P.Ty) (value : ExprOrNondet P)

/-- The label or name identifying a path condition entry. -/
def PathConditionEntry.name {P : PureExpr} [ToFormat P.Ident] : PathConditionEntry P → String
  | .assumption label _ => label
  | .varDecl name _ _ => toString (f!"{name}")

instance [BEq P.Ident] [BEq P.Ty] [BEq P.Expr] : BEq (PathConditionEntry P) where
  beq
    | .assumption l1 e1, .assumption l2 e2 => l1 == l2 && e1 == e2
    | .varDecl n1 t1 (.det e1), .varDecl n2 t2 (.det e2) => n1 == n2 && t1 == t2 && e1 == e2
    | .varDecl n1 t1 .nondet, .varDecl n2 t2 .nondet => n1 == n2 && t1 == t2
    | _, _ => false

@[expose] abbrev PathCondition (P : PureExpr)  := List (PathConditionEntry P)
@[expose] abbrev PathConditions (P : PureExpr) := List (PathCondition P)

def PathConditionEntry.format' {P} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] : PathConditionEntry P → Format
  | .assumption label expr => f!"({label}, {expr})"
  | .varDecl name ty (.det e) => f!"(init {name} : {ty} := {e})"
  | .varDecl name ty .nondet => f!"(init {name} : {ty})"

instance [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] : ToFormat (PathConditionEntry P) where
  format := PathConditionEntry.format'

def PathCondition.format' {P} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] (m : PathCondition P) : Format :=
  match m with
  | [] => ""
  | [e] => PathConditionEntry.format' e
  | e :: rest =>
    f!"{PathConditionEntry.format' e}\n" ++ PathCondition.format' rest

def PathConditions.format' {P} [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] (ms : PathConditions P) : Format :=
  match ms with
  | [] => ""
  | [m] => f!"[{PathCondition.format' m}]"
  | m :: rest =>
    f!"[{PathCondition.format' m}]\n" ++
    PathConditions.format' rest

instance [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] : ToFormat (PathCondition P) where
  format p := PathCondition.format' p

instance [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] : ToFormat (PathConditions P) where
  format p := PathConditions.format' p

def PathConditions.newest (ps : PathConditions P) : PathCondition P :=
  match ps with
  | [] => []
  | p :: _ => p

def PathConditions.pop (ps : PathConditions P) : PathConditions P :=
  match ps with
  | [] => []
  | _ :: rest => rest

def PathConditions.push (ps : PathConditions P) (p : PathCondition P): PathConditions P :=
  p :: ps

def PathConditions.addEntry (ps : PathConditions P) (e : PathConditionEntry P) : PathConditions P :=
  match ps with
  | [] => [[e]]
  | p :: ps => (p ++ [e]) :: ps

def PathConditions.addInNewest (ps : PathConditions P) (m : PathCondition P) : PathConditions P :=
  let new := ps.newest ++ m
  let ps := ps.pop
  ps.push new

/-- Remove path condition entries with specified names -/
def PathConditions.removeByNames [ToFormat P.Ident] (ps : PathConditions P) (names : List String) : PathConditions P :=
  ps.map (fun pc => pc.filter (fun e => !names.contains e.name))

inductive PropertyType where
  | cover
  | assert
  | divisionByZero
  | arithmeticOverflow
  | outOfBoundsAccess
  deriving Repr, DecidableEq

/-- Whether an unreachable path counts as pass for this property type.
    Assertions pass vacuously when unreachable; covers fail. -/
def PropertyType.passWhenUnreachable : PropertyType → Bool
  | .assert | .divisionByZero | .arithmeticOverflow | .outOfBoundsAccess => true
  | .cover => false

instance : ToFormat PropertyType where
  format p := match p with
    | .cover => "cover"
    | .assert => "assert"
    | .divisionByZero => "division by zero check"
    | .arithmeticOverflow => "arithmetic overflow check"
    | .outOfBoundsAccess => "out-of-bounds access check"

/--
A proof obligation can be discharged by some backend solver or a dedicated
decision procedure or via denotation into Lean.
-/
structure ProofObligation (P : PureExpr) where
  label : String
  property : PropertyType
  assumptions : PathConditions P
  obligation : P.Expr
  metadata : MetaData P

instance [BEq P.Ident] [BEq P.Ty] [BEq P.Expr] [BEq (MetaData P)] : BEq (ProofObligation P) where
  beq a b :=
    a.label == b.label &&
    a.assumptions == b.assumptions &&
    a.obligation == b.obligation &&
    a.metadata == b.metadata

instance [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat P.Expr] : ToFormat (ProofObligation P) where
  format ob := f!"Label: {ob.label}\n\
                  Property : {ob.property}\n\
                  Assumptions: {PathConditions.format' ob.assumptions}\n\
                  Obligation: {ob.obligation}\n\
                  Metadata: {ob.metadata}\n"

@[expose] abbrev ProofObligations (P : PureExpr) := Array (ProofObligation P)

---------------------------------------------------------------------

class EvalContext (P : PureExpr) (State : Type) where
  /- Evaluation utilities -/
  eval              : State → P.Expr → P.Expr
  updateError       : State → EvalError P → State
  lookupError       : State → Option (EvalError P)
  update            : State → P.Ident → P.Ty → P.Expr → State
  lookup            : State → P.Ident → Option P.TypedExpr
  preprocess        : State → Cmd P → P.Expr → (P.Expr × State)
  genFreeVar        : State → P.Ident → P.Ty → (P.Expr × State)
  denoteBool        : P.Expr → Option Bool

  addWarning        : State → EvalWarning P → State

  /- Path conditions and proof obligations collected during evaluation -/
  getPathConditions : State → (PathConditions P)
  addPathCondition  : State → (PathCondition P) → State
  deferObligation   : State → (ProofObligation P) → State

  -- /-- If two states give the same result to all `lookup` calls, they also
  -- give the same result to all `eval` calls. -/
  -- lookupEval : (s1 : State) → (s2 : State) → (∀ x, lookup s1 x = lookup s2 x) →
  --              (∀ e, eval s1 e = eval s2 e)

---------------------------------------------------------------------

end -- public section
end Imperative
