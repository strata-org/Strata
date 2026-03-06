/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.TermType
import Lean.Elab.Command

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
  id : String
  ty : TermType
deriving Repr, DecidableEq, Inhabited, Hashable

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

inductive Op.Core : Type where
  ---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------
  | not
  | and
  | or
  | eq
  | ite
  | implies
  | distinct
  | uf : UF → Op.Core
  deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op.Num : Type where
  ---------- SMTLib core theory of integers (`Ints`) and reals (`Reals`) ----------
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
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op.BV : Type where
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
  | bvashr
  | bvslt
  | bvsle
  | bvult
  | bvsge
  | bvsgt
  | bvule
  | bvugt
  | bvuge
  | bvudiv
  | bvurem
  | bvsdiv
  | bvsrem
  | bvnego  -- bit-vector negation overflow predicate
  | bvsaddo -- bit-vector signed addition overflow predicate
  | bvssubo -- bit-vector signed subtraction overflow predicate
  | bvsmulo -- bit-vector signed multiplication overflow predicate
  | bvconcat
  | zero_extend : Nat → Op.BV
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op.Strings : Type where
  ---------- SMTLib theory of unicode strings and regular expressions (`Strings`) ----------
  -- Strings
  | str_length
  | str_concat
  | str_lt
  | str_le
  | str_at
  | str_substr
  | str_prefixof
  | str_suffixof
  | str_contains
  | str_indexof
  | str_replace
  | str_replace_all
  -- Regular Expressions
  | str_to_re
  | str_in_re
  | re_none    -- constant
  | re_all     -- constant
  | re_allchar -- constant
  | re_concat
  | re_union
  | re_inter
  | re_star
  | str_replace_re
  | str_replace_re_all
  | re_comp
  | re_diff
  | re_plus
  | re_opt
  | re_range
  | re_loop : Nat → Nat → Op.Strings
  | re_index : Nat → Op.Strings
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op.Arrays : Type where
  ---------- SMTLib theory of arrays (`ArraysEx`) ----------
  | select
  | store
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op.DatatypeFuncs : Type where
  | constructor : Op.DatatypeFuncs
  | tester : Op.DatatypeFuncs
  | selector : Op.DatatypeFuncs
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Op : Type where
  -- SMTLib core theory of equality with uninterpreted functions (`UF`)
  | core : Op.Core → Op
  -- SMTLib core theory of integers (`Ints`) and reals (`Reals`)
  | num : Op.Num → Op
  -- SMTLib theory of finite bitvectors (`BV`)
  | bv : Op.BV → Op
  -- SMTLib theory of unicode strings and regular expressions (`Strings`)
  | str : Op.Strings → Op
  -- SMTLib theory of arrays (`ArraysEx`)
  | arr : Op.Arrays → Op
  -- An operator to group triggers together
  | triggers
  -- Core ADT operators with a trusted mapping to SMT
  | option_get
  -- Datatype ops (for user-defined algebraic datatypes)
  | datatype_op : Op.DatatypeFuncs → String → Op
deriving Repr, DecidableEq, Inhabited, Hashable

-- Generate abbreviations like `Op.not` for `Op.core Op.Core.not` for
-- convenience.
open Lean Elab Command Lean.Name in
elab "#genOpAbbrevs" : command => do
  let env ← getEnv
  let mut abbrevs : Array (Name × (TSyntax `command)) := #[]

  if let some (.inductInfo coreInfo) := env.find? `Strata.SMT.Op.Core then
    for ctor in coreInfo.ctors do
      let ctorName := ctor.toString.splitToList (· == '.') |>.getLast!
      let name := Lean.Name.mkStr2 "Op" ctorName
      if ctorName == "uf" then
        let abbrevCmd ← `(command| abbrev $(mkIdent name) (arg : UF) := Op.core (Op.Core.uf arg))
        abbrevs := abbrevs.push (name, abbrevCmd)
      else
        let abbrevCmd ← `(command| abbrev $(mkIdent name) := Op.core $(mkIdent ctor))
        abbrevs := abbrevs.push (name, abbrevCmd)

  if let some (.inductInfo numInfo) := env.find? `Strata.SMT.Op.Num then
    for ctor in numInfo.ctors do
      let ctorName := ctor.toString.splitToList (· == '.') |>.getLast!
      let name := Lean.Name.mkStr2 "Op" ctorName
      let abbrevCmd ← `(command| abbrev $(mkIdent name) := Op.num $(mkIdent ctor))
      abbrevs := abbrevs.push (name, abbrevCmd)

  if let some (.inductInfo bvInfo) := env.find? `Strata.SMT.Op.BV then
    for ctor in bvInfo.ctors do
      let ctorName := ctor.toString.splitToList (· == '.') |>.getLast!
      let name := Lean.Name.mkStr2 "Op" ctorName
      if ctorName == "zero_extend" then
        let abbrevCmd ← `(command| abbrev $(mkIdent name) (n : Nat) := Op.bv (Op.BV.zero_extend n))
        abbrevs := abbrevs.push (name, abbrevCmd)
      else
        let abbrevCmd ← `(command| abbrev $(mkIdent name) := Op.bv $(mkIdent ctor))
        abbrevs := abbrevs.push (name, abbrevCmd)

  if let some (.inductInfo strInfo) := env.find? `Strata.SMT.Op.Strings then
    for ctor in strInfo.ctors do
      let ctorName := ctor.toString.splitToList (· == '.') |>.getLast!
      let name := Lean.Name.mkStr2 "Op" ctorName
      if ctorName == "re_index" then
        let abbrevCmd ← `(command| abbrev $(mkIdent name) (n : Nat) := Op.str (Op.Strings.re_index n))
        abbrevs := abbrevs.push (name, abbrevCmd)
      else if ctorName == "re_loop" then
        let abbrevCmd ← `(command| abbrev $(mkIdent name) (n1 n2 : Nat) := Op.str (Op.Strings.re_loop n1 n2))
        abbrevs := abbrevs.push (name, abbrevCmd)
      else
        let abbrevCmd ← `(command| abbrev $(mkIdent name) := Op.str $(mkIdent ctor))
        abbrevs := abbrevs.push (name, abbrevCmd)

  if let some (.inductInfo arrInfo) := env.find? `Strata.SMT.Op.Arrays then
    for ctor in arrInfo.ctors do
      let ctorName := ctor.toString.splitToList (· == '.') |>.getLast!
      let name := Lean.Name.mkStr2 "Op" ctorName
      let abbrevCmd ← `(command| abbrev $(mkIdent name) := Op.arr $(mkIdent ctor))
      abbrevs := abbrevs.push (name, abbrevCmd)

  for a in abbrevs do
    elabCommand a.snd
  logInfo s!"Generated abbrevs: {abbrevs.map (fun a => a.fst)}"


/--
info: Generated abbrevs: #[Op.not, Op.and, Op.or, Op.eq, Op.ite, Op.implies, Op.distinct, Op.uf, Op.neg, Op.sub, Op.add, Op.mul, Op.div, Op.mod, Op.abs, Op.le, Op.lt, Op.ge, Op.gt, Op.bvneg, Op.bvadd, Op.bvsub, Op.bvmul, Op.bvnot, Op.bvand, Op.bvor, Op.bvxor, Op.bvshl, Op.bvlshr, Op.bvashr, Op.bvslt, Op.bvsle, Op.bvult, Op.bvsge, Op.bvsgt, Op.bvule, Op.bvugt, Op.bvuge, Op.bvudiv, Op.bvurem, Op.bvsdiv, Op.bvsrem, Op.bvnego, Op.bvsaddo, Op.bvssubo, Op.bvsmulo, Op.bvconcat, Op.zero_extend, Op.str_length, Op.str_concat, Op.str_lt, Op.str_le, Op.str_at, Op.str_substr, Op.str_prefixof, Op.str_suffixof, Op.str_contains, Op.str_indexof, Op.str_replace, Op.str_replace_all, Op.str_to_re, Op.str_in_re, Op.re_none, Op.re_all, Op.re_allchar, Op.re_concat, Op.re_union, Op.re_inter, Op.re_star, Op.str_replace_re, Op.str_replace_re_all, Op.re_comp, Op.re_diff, Op.re_plus, Op.re_opt, Op.re_range, Op.re_loop, Op.re_index, Op.select, Op.store]
-/
#guard_msgs in
#genOpAbbrevs

def Op.mkName : Op → String
  | .not           => "not"
  | .and           => "and"
  | .or            => "or"
  | .eq            => "="
  | .ite           => "ite"
  | .implies       => "=>"
  | .distinct      => "distinct"
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
  | .bvashr        => "bvashr"
  | .bvlshr        => "bvlshr"
  | .bvslt         => "bvslt"
  | .bvsle         => "bvsle"
  | .bvsgt         => "bvsgt"
  | .bvsge         => "bvsge"
  | .bvult         => "bvult"
  | .bvule         => "bvule"
  | .bvugt         => "bvugt"
  | .bvuge         => "bvuge"
  | .bvudiv        => "bvudiv"
  | .bvurem        => "bvurem"
  | .bvsdiv        => "bvsdiv"
  | .bvsrem        => "bvsrem"
  | .bvnego        => "bvnego"
  | .bvsaddo       => "bvsaddo"
  | .bvssubo       => "bvssubo"
  | .bvsmulo       => "bvsmulo"
  | .bvconcat      => "concat"
  | .zero_extend _ => "zero_extend"
  | .triggers      => "triggers"
  | .option_get    => "option.get"
  | .datatype_op .tester name => s!"is-{name}"
  | .datatype_op _ name => name
  | .str_length    => "str.len"
  | .str_concat    => "str.++"
  | .str_lt        => "str.<"
  | .str_to_re     => "str.to_re"
  | .str_in_re     => "str.in_re"
  | .re_none       => "re.none"
  | .re_all        => "re.all"
  | .re_allchar    => "re.allchar"
  | .re_plus       => "re.+"
  | .re_concat     => "re.++"
  | .re_union      => "re.union"
  | .re_inter      => "re.inter"
  | .re_star       => "re.*"
  | .str_le        => "str.<="
  | .str_at        => "str.at"
  | .str_substr    => "str.substr"
  | .str_prefixof  => "str.prefixof"
  | .str_suffixof  => "str.suffixof"
  | .str_contains  => "str.contains"
  | .str_indexof   => "str.indexof"
  | .str_replace   => "str.replace"
  | .str_replace_all => "str.replace_all"
  | .str_replace_re  => "str.replace_re"
  | .str_replace_re_all => "str.replace_re_all"
  | .re_comp       => "re.comp"
  | .re_diff       => "re.diff"
  | .re_opt        => "re.opt"
  | .re_range      => "re.range"
  | .re_index _    => "re.^"
  | .re_loop _ _   => "re.loop"
  | .select        => "select"
  | .store         => "store"

def Op.LT : Op → Op → Bool
  | .uf f₁, .uf f₂                    => f₁ < f₂
  | .zero_extend n₁, .zero_extend n₂  => n₁ < n₂
  | .re_index n₁, .re_index n₂        => n₁ < n₂
  | .re_loop n₁ n₂, .re_loop m₁ m₂    => n₁ < n₂ && m₁ < m₂
  | ty₁, ty₂                          => ty₁.mkName < ty₂.mkName

instance : LT Op where
  lt := fun x y => Op.LT x y

instance Op.decLt (x y : Op) : Decidable (x < y) :=
  if h : Op.LT x y then isTrue h else isFalse h

end Strata.SMT
