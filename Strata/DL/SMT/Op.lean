/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.TermType

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Op.lean)
This file defines the operators on Terms. See `Term.lean` for the
definition of the Term language.

There are three kinds of term operators:
1. Operators that map directly to an underlying SMT theory
2. Operators for constructing and destructing core ADTs that are lowered to SMT
   by a trusted code generation pass. This also includes core operators whose
   semantics we don't model in the Term language (but rather directly in SMT).
3. Operators for destructing extension ADTs, also lowered by the trusted pass.

We embed SMT and core ADT operators directly into the top-level `Op` ADT, to
simplify pattern matching against them within rewrite rules.
-/

namespace Strata.SMT

structure TermVar where
  isBound : Bool
  id : String
  ty : TermType
deriving Repr, DecidableEq, Inhabited

def TermVar.lt (v v' : TermVar) : Bool :=
  v.id < v'.id || (v.id = v'.id && v.ty < v'.ty)

instance : LT TermVar where
  lt := fun x y => TermVar.lt x y

instance TermVar.decLt (x y : TermVar) : Decidable (x < y) :=
  if h : TermVar.lt x y then isTrue h else isFalse h

structure UF where
  id : String
  args : List TermVar
  out : TermType
deriving Repr, DecidableEq, Inhabited

def UF.lt (uf uf' : UF) : Bool :=
  uf.id < uf'.id ||
  (uf.id = uf'.id && uf.args < uf'.args) ||
  (uf.id = uf'.id && uf.args = uf'.args && uf.out < uf'.out)

instance : LT UF where
  lt := fun x y => UF.lt x y

instance UF.decLt (x y : UF) : Decidable (x < y) :=
  if h : UF.lt x y then isTrue h else isFalse h

instance : Hashable UF where
  hash := λ a => hash s!"{repr a}"

inductive Op : Type where
  ---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------
  | not
  | and
  | or
  | eq
  | ite
  | implies
  | uf : UF → Op
  ---------- SMTLib core theory of integers (`Ints`) ----------
  -- The theory of Reals also supports all operations, except
  -- `mod` and `abs`, below.
  | neg
  | sub
  | add
  | mul
  | div
  | mod
  | abs
  | le
  | lt
  | ge
  | gt
  ---------- SMTLib theory of finite bitvectors (`BV`) ----------
  | bvneg
  | bvadd
  | bvsub
  | bvmul
  | bvnot
  | bvand
  | bvor
  | bvxor
  | bvshl
  | bvlshr
  | bvslt
  | bvsle
  | bvult
  | bvule
  | bvugt
  | bvuge
  | bvudiv
  | bvurem
  | bvnego  -- bit-vector negation overflow predicate
  | bvsaddo -- bit-vector signed addition overflow predicate
  | bvssubo -- bit-vector signed subtraction overflow predicate
  | bvsmulo -- bit-vector signed multiplication overflow predicate
  | bvconcat
  | zero_extend : Nat → Op
  ---------- SMTLib theory of unicode strings (`Strings`) ----------
  | str_length
  | str_concat
  ---------- An operator to group triggers together
  | triggers
  ---------- Core ADT operators with a trusted mapping to SMT ----------
  | option_get
deriving Repr, DecidableEq, Inhabited, Hashable


def Op.mkName : Op → String
  | .not           => "not"
  | .and           => "and"
  | .or            => "or"
  | .eq            => "eq"
  | .ite           => "ite"
  | .implies       => "=>"
  | .uf u          => s!"{u.id}"
  | .neg           => "-"
  | .sub           => "-"
  | .add           => "+"
  | .mul           => "*"
  | .bvnot         => "bvnot"
  | .bvand         => "bvand"
  | .bvor          => "bvor"
  | .bvxor         => "bvxor"
  | .div           => "div"
  | .mod           => "mod"
  | .abs           => "abs"
  | .le            => "<="
  | .lt            => "<"
  | .ge            => ">="
  | .gt            => ">"
  | .bvneg         => "bvneg"
  | .bvadd         => "bvadd"
  | .bvsub         => "bvsub"
  | .bvmul         => "bvmul"
  | .bvshl         => "bvshl"
  | .bvlshr        => "bvlshr"
  | .bvslt         => "bvslt"
  | .bvsle         => "bvsle"
  | .bvult         => "bvult"
  | .bvule         => "bvule"
  | .bvugt         => "bvugt"
  | .bvuge         => "bvuge"
  | .bvudiv        => "bvudiv"
  | .bvurem        => "bvurem"
  | .bvnego        => "bvnego"
  | .bvsaddo       => "bvsaddo"
  | .bvssubo       => "bvssubo"
  | .bvsmulo       => "bvsmulo"
  | .bvconcat      => "concat"
  | .zero_extend _ => "zero_extend"
  | .str_length    => "str.len"
  | .str_concat    => "str.++"
  | .triggers      => "triggers"
  | .option_get    => "option.get"

def Op.LT : Op → Op → Bool
  | .uf f₁, uf f₂                    => f₁ < f₂
  | .zero_extend n₁, .zero_extend n₂ => n₁ < n₂
  | ty₁, ty₂                         => ty₁.mkName < ty₂.mkName

instance : LT Op where
  lt := fun x y => Op.LT x y

instance Op.decLt (x y : Op) : Decidable (x < y) :=
  if h : Op.LT x y then isTrue h else isFalse h

end Strata.SMT
