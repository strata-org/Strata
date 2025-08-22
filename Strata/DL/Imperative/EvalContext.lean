/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.EvalError
import Strata.DL.Imperative.MetaData
import Strata.DL.Util.ListMap
import Strata.DL.Util.Maps

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

abbrev PathCondition (P : PureExpr)  := ListMap String P.Expr
abbrev PathConditions (P : PureExpr) := List (PathCondition P)

def PathCondition.format' {P} [ToFormat P.Expr] (m : PathCondition P) : Format :=
  match m with
  | [] => ""
  | [(k, v)] => f!"({k}, {v})"
  | (k, v) :: rest =>
    f!"({k}, {v})\n" ++ PathCondition.format' rest

def PathConditions.format' {P} [ToFormat P.Expr] (ms : PathConditions P) : Format :=
  match ms with
  | [] => ""
  | [m] => f!"[{PathCondition.format' m}]"
  | m :: rest =>
    f!"[{PathCondition.format' m}]\n" ++
    PathConditions.format' rest

instance [ToFormat P.Expr] : ToFormat (PathCondition P) where
  format p := PathCondition.format' p

instance [ToFormat P.Expr] : ToFormat (PathConditions P) where
  format p := PathConditions.format' p

def PathConditions.newest (ps : PathConditions P) : PathCondition P :=
  match ps with
  | [] => .empty
  | p :: _ => p

def PathConditions.pop (ps : PathConditions P) : PathConditions P :=
  match ps with
  | [] => []
  | _ :: rest => rest

def PathConditions.push (ps : PathConditions P) (p : PathCondition P): PathConditions P :=
  p :: ps

def PathConditions.insert (ps : PathConditions P) (l : String) (e : P.Expr) :=
  match ps with
  | [] => [Map.ofList [(l, e)]]
  | p :: ps => Map.insert p l e :: ps

def PathConditions.addInNewest (ps : PathConditions P) (m : PathCondition P) : PathConditions P :=
  let new := ps.newest ++ m
  let ps := ps.pop
  ps.push new

/--
A proof obligation can be discharged by some backend solver or a dedicated
decision procedure or via denotation into Lean.
-/
structure ProofObligation (P : PureExpr) where
  label : String
  assumptions : PathConditions P
  obligation : P.Expr
  metadata : MetaData P

instance [BEq P.Ident] [BEq P.Expr] [BEq (MetaData P)] : BEq (ProofObligation P) where
  beq a b :=
    a.label == b.label &&
    a.assumptions == b.assumptions &&
    a.obligation == b.obligation &&
    a.metadata == b.metadata

instance [ToFormat P.Ident] [ToFormat P.Expr] : ToFormat (ProofObligation P) where
  format ob := f!"Label: {ob.label}\n\
                  Assumptions: {PathConditions.format' ob.assumptions}\n\
                  Obligation: {ob.obligation}\n\
                  Metadata: {ob.metadata}\n"

abbrev ProofObligations (P : PureExpr) := Array (ProofObligation P)

---------------------------------------------------------------------

class EvalContext (P : PureExpr) (State : Type) where
  /- Evaluation utilities -/
  eval              : State → P.Expr → P.Expr
  updateError       : State → EvalError P → State
  lookupError       : State → Option (EvalError P)
  update            : State → P.Ident → P.Ty → P.Expr → State
  lookup            : State → P.Ident → Option P.TypedExpr
  preprocess        : State → P.Expr → (P.Expr × State)
  genFreeVar        : State → P.Ident → P.Ty → (P.Expr × State)
  denoteBool        : P.Expr → Option Bool

  /- Path conditions and proof obligations collected during evaluation -/
  getPathConditions : State → (PathConditions P)
  addPathCondition  : State → (PathCondition P) → State
  deferObligation   : State → (ProofObligation P) → State

  -- /-- If two states give the same result to all `lookup` calls, they also
  -- give the same result to all `eval` calls. -/
  -- lookupEval : (s1 : State) → (s2 : State) → (∀ x, lookup s1 x = lookup s2 x) →
  --              (∀ e, eval s1 e = eval s2 e)

---------------------------------------------------------------------

end Imperative
