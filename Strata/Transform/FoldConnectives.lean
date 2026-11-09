/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.NameMangling
public import Strata.Transform.Simplify.Expr

/-! # Folding boolean connectives with a literal argument

The evaluator decides `and`, `or` and `==>` only on a literal first argument.
`foldConnectives` decides them on a literal second argument too. Dropping an
operand keeps the term's value when every operand is a boolean with a defined
value: Core terms have no side effects, and function preconditions must
already be lowered to assertions. The evaluator needs no such condition: it
drops only a second operand, whose preconditions are checked only when the
first operand does not decide the result. -/

namespace Core.FoldConnectives

open Lambda

public section

/-- The boolean connective the op `name` denotes, read through name mangling.
    The type checker rejects a program function with a factory function's
    name, so only the factory's connectives match. -/
def boolOpOf? (name : String) : Option BoolOpKind :=
  match CoreOp.ofString (NameMangling.demangledBaseName name) with
  | .bool k => some k
  | _ => none

/-- Top-level conjuncts of `e`, splitting `Bool.And` and nothing else. A
    disjunction, a negation or a binder comes back whole, since a comparison inside
    one need not hold of every index. -/
def conjuncts : LExpr CoreLParams.mono → List (LExpr CoreLParams.mono)
  | e@(.app _ (.app _ (.op _ o _) x) y) =>
    if boolOpOf? o.name == some .And then conjuncts x ++ conjuncts y else [e]
  | e => [e]

/-- The value of `e` when it is an `and`, `or` or `==>` with a literal
    argument. `a ==> false` is left as is: its value `!a` is neither a literal
    nor an operand. -/
def connectiveValue? (e : LExpr CoreLParams.mono) :
    Option (LExpr CoreLParams.mono) :=
  match e with
  | .app _ (.app _ (.op _ o _) x) y =>
    match boolOpOf? o.name, x.denoteBool, y.denoteBool with
    | some .And, some false, _ | some .And, _, some false =>
      some (.boolConst () false)
    | some .And, some true, _ => some y
    | some .And, _, some true => some x
    | some .Or, some true, _ | some .Or, _, some true =>
      some (.boolConst () true)
    | some .Or, some false, _ => some y
    | some .Or, _, some false => some x
    | some .Implies, some false, _ | some .Implies, _, some true =>
      some (.boolConst () true)
    | some .Implies, some true, _ => some y
    | _, _, _ => none
  | _ => none

/-- Applies `connectiveValue?` bottom up, under binders but not in
    triggers. -/
def foldConnectives (e : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  (Simplify.rewriteUp [connectiveValue?] none e).fst

end -- public section

end Core.FoldConnectives
