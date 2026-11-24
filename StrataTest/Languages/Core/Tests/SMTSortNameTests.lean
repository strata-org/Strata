/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # User sorts named like solver built-in sorts

cvc5 and z3 already define sorts with these names. Declaring one of them is not a fresh
sort: z3 rejects the declaration, and cvc5 can keep its own sort, with its own cardinality
(its `Tuple Bool` has two values, `Nullable Bool` three). Each type below is uninterpreted
in Strata, so five pairwise-distinct values are consistent and every `assert false` must
fail, on both solvers. The encoder emits each such sort under `Core.smtSortName`. -/

meta section
open Strata

private def builtinNamePgm :=
#strata
program Core;

type Array (a : Type);
type Bag (a : Type);
type BitVec (a : Type);
type Bool (a : Type);
type FiniteField (a : Type);
type Float128 (a : Type);
type Float16 (a : Type);
type Float32 (a : Type);
type Float64 (a : Type);
type FloatingPoint (a : Type);
type Int (a : Type);
type List (a : Type);
type Nullable (a : Type);
type Real (a : Type);
type RegEx (a : Type);
type RegLan (a : Type);
type Relation (a : Type);
type RoundingMode (a : Type);
type Seq (a : Type);
type String (a : Type);
type Table (a : Type);
type Tuple (a : Type);
type Unicode (a : Type);
type UnitTuple (a : Type);
type bv (a : Type);
type StringSequence (a : Type);

procedure CardArray(a : Array bool, b : Array bool, c : Array bool, d : Array bool, e : Array bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Array]: false;
};

procedure CardBag(a : Bag bool, b : Bag bool, c : Bag bool, d : Bag bool, e : Bag bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Bag]: false;
};

procedure CardBitVec(a : BitVec bool, b : BitVec bool, c : BitVec bool, d : BitVec bool, e : BitVec bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [BitVec]: false;
};

procedure CardBool(a : Bool bool, b : Bool bool, c : Bool bool, d : Bool bool, e : Bool bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Bool]: false;
};

procedure CardFiniteField(a : FiniteField bool, b : FiniteField bool, c : FiniteField bool, d : FiniteField bool, e : FiniteField bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [FiniteField]: false;
};

procedure CardFloat128(a : Float128 bool, b : Float128 bool, c : Float128 bool, d : Float128 bool, e : Float128 bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Float128]: false;
};

procedure CardFloat16(a : Float16 bool, b : Float16 bool, c : Float16 bool, d : Float16 bool, e : Float16 bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Float16]: false;
};

procedure CardFloat32(a : Float32 bool, b : Float32 bool, c : Float32 bool, d : Float32 bool, e : Float32 bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Float32]: false;
};

procedure CardFloat64(a : Float64 bool, b : Float64 bool, c : Float64 bool, d : Float64 bool, e : Float64 bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Float64]: false;
};

procedure CardFloatingPoint(a : FloatingPoint bool, b : FloatingPoint bool, c : FloatingPoint bool, d : FloatingPoint bool, e : FloatingPoint bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [FloatingPoint]: false;
};

procedure CardInt(a : Int bool, b : Int bool, c : Int bool, d : Int bool, e : Int bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Int]: false;
};

procedure CardList(a : List bool, b : List bool, c : List bool, d : List bool, e : List bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [List]: false;
};

procedure CardNullable(a : Nullable bool, b : Nullable bool, c : Nullable bool, d : Nullable bool, e : Nullable bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Nullable]: false;
};

procedure CardReal(a : Real bool, b : Real bool, c : Real bool, d : Real bool, e : Real bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Real]: false;
};

procedure CardRegEx(a : RegEx bool, b : RegEx bool, c : RegEx bool, d : RegEx bool, e : RegEx bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [RegEx]: false;
};

procedure CardRegLan(a : RegLan bool, b : RegLan bool, c : RegLan bool, d : RegLan bool, e : RegLan bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [RegLan]: false;
};

procedure CardRelation(a : Relation bool, b : Relation bool, c : Relation bool, d : Relation bool, e : Relation bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Relation]: false;
};

procedure CardRoundingMode(a : RoundingMode bool, b : RoundingMode bool, c : RoundingMode bool, d : RoundingMode bool, e : RoundingMode bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [RoundingMode]: false;
};

procedure CardSeq(a : Seq bool, b : Seq bool, c : Seq bool, d : Seq bool, e : Seq bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Seq]: false;
};

procedure CardString(a : String bool, b : String bool, c : String bool, d : String bool, e : String bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [String]: false;
};

procedure CardTable(a : Table bool, b : Table bool, c : Table bool, d : Table bool, e : Table bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Table]: false;
};

procedure CardTuple(a : Tuple bool, b : Tuple bool, c : Tuple bool, d : Tuple bool, e : Tuple bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Tuple]: false;
};

procedure CardUnicode(a : Unicode bool, b : Unicode bool, c : Unicode bool, d : Unicode bool, e : Unicode bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [Unicode]: false;
};

procedure CardUnitTuple(a : UnitTuple bool, b : UnitTuple bool, c : UnitTuple bool, d : UnitTuple bool, e : UnitTuple bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [UnitTuple]: false;
};

procedure CardStringSequence(a : StringSequence bool, b : StringSequence bool, c : StringSequence bool, d : StringSequence bool, e : StringSequence bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [StringSequence]: false;
};

procedure Cardbv(a : bv bool, b : bv bool, c : bv bool, d : bv bool, e : bv bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [bv]: false;
};
#end

/-- Each obligation's label and verdict, one per line. -/
private def verdicts (pgm : StrataDDM.Program) (options : Core.VerifyOptions) : IO Unit := do
  let results ← Strata.Core.verify pgm (options := { options with verbose := .quiet })
  for r in results do
    let verdict := match r.outcome with
      | .ok o => _root_.Core.VCOutcome.label o r.obligation.property r.checkLevel r.checkMode
      | .error e => s!"error: {e}"
    IO.println s!"{r.obligation.label}: {verdict}"

/--
info: Array: fail
Bag: fail
BitVec: fail
Bool: fail
FiniteField: fail
Float128: fail
Float16: fail
Float32: fail
Float64: fail
FloatingPoint: fail
Int: fail
List: fail
Nullable: fail
Real: fail
RegEx: fail
RegLan: fail
Relation: fail
RoundingMode: fail
Seq: fail
String: fail
Table: fail
Tuple: fail
Unicode: fail
UnitTuple: fail
StringSequence: fail
bv: fail
-/
#guard_msgs in
#eval verdicts builtinNamePgm Core.VerifyOptions.default

/--
info: Array: fail
Bag: fail
BitVec: fail
Bool: fail
FiniteField: fail
Float128: fail
Float16: fail
Float32: fail
Float64: fail
FloatingPoint: fail
Int: fail
List: fail
Nullable: fail
Real: fail
RegEx: fail
RegLan: fail
Relation: fail
RoundingMode: fail
Seq: fail
String: fail
Table: fail
Tuple: fail
Unicode: fail
UnitTuple: fail
StringSequence: fail
bv: fail
-/
#guard_msgs in
#eval verdicts builtinNamePgm { Core.VerifyOptions.default with solver := "z3" }

/-! ## Model values under Core sort names

A solver names its abstract values after their (renamed) sort; counterexamples show
them under the Core name. -/

#guard Core.coreSortNamesIn "@($__Strata_Set Int)_0" == "@(Set Int)_0"
#guard Core.coreSortNamesIn "$__Strata_Tuple!val!3" == "Tuple!val!3"
#guard Core.coreSortNamesIn "@($__Strata_$__Strata_Set ($__Strata_Set Int))_1" ==
  "@($__Strata_Set (Set Int))_1"
#guard Core.coreSortNamesIn "x@1" == "x@1"
#guard Core.coreSortNamesIn "$__Strata_$__Strata_$__Strata_X!val!0" == "$__Strata_$__Strata_X!val!0"
#guard Core.coreSortNamesIn "a $__Strata_Set b $__Strata_" == "a Set b "
-- A prefix inside a name is not one `smtSortName` added.
#guard Core.coreSortNamesIn "A$__Strata_B!val!0" == "A$__Strata_B!val!0"
-- Only names the solver made up are mapped: a user's name is left as it is.
#guard Core.coreValueName "$__Strata_Set!val!0" == "Set!val!0"
#guard Core.coreValueName "@($__Strata_Set Int)_0" == "@(Set Int)_0"
#guard Core.coreValueName "$__Strata_x" == "$__Strata_x"

private def setEqPgm :=
#strata
program Core;

procedure SetEq(s : Set int, t : Set int)
{
  assert [eq]: s == t;
};
#end

/-- Whether each failed obligation has a counterexample, and whether it shows the renamed
    sort name anywhere. -/
private def modelNames (options : Core.VerifyOptions) : IO Unit := do
  let results ← Strata.Core.verify setEqPgm (options := { options with verbose := .quiet })
  for r in results do
    let shown := toString (Std.format r.lexprModel)
    IO.println s!"{r.obligation.label}: model: {!r.lexprModel.isEmpty}, \
      renamed sort shown: {decide ((shown.splitOn Core.smtSortPrefix).length > 1)}"

/-- info: eq: model: true, renamed sort shown: false -/
#guard_msgs in
#eval modelNames Core.VerifyOptions.default

/-- info: eq: model: true, renamed sort shown: false -/
#guard_msgs in
#eval modelNames { Core.VerifyOptions.default with solver := "z3" }

/-! ## Constructors named like solver functions

cvc5 rejects a `declare-fun` that shadows one of its theory functions (`seq.len`,
`set.member`, ...). A datatype's constructors and selectors are declared with the
datatype instead, and both solvers keep them apart from the theory functions. -/

private def ctorNamePgm :=
#strata
program Core;

datatype D { seq.len(x : int), set.member() };

procedure Ctors(d : D)
{
  assume [is_len_one]: D..isseq.len(d) && D..x(d) == 1;
  assert [rebuilt]: d == seq.len(1);
  assert [not_member]: !(d == set.member());
};
#end

/--
info: assume_is_len_one_calls_D..x_0: pass
rebuilt: pass
not_member: pass
-/
#guard_msgs in
#eval verdicts ctorNamePgm Core.VerifyOptions.default

/--
info: assume_is_len_one_calls_D..x_0: pass
rebuilt: pass
not_member: pass
-/
#guard_msgs in
#eval verdicts ctorNamePgm { Core.VerifyOptions.default with solver := "z3" }

/-! ## A user type named with the renaming's prefix

A user type `$__Strata_Set` is unrelated to Core's `Set`, so an axiom about it says
nothing about `Set`, and `assert false` must not pass. The renaming keeps them apart.
The solvers answer unknown rather than fail because of the quantified axiom. -/

private def prefixClashPgm :=
#strata
program Core;

type $__Strata_Set (a : Type);
axiom [one]: forall x : $__Strata_Set bool, y : $__Strata_Set bool :: x == y;

procedure Q(a : Set bool, b : Set bool)
{
  assume [ne]: !(a == b);
  assert [clash]: false;
};
#end

/-- info: clash: unknown -/
#guard_msgs in
#eval verdicts prefixClashPgm Core.VerifyOptions.default

/-- info: clash: unknown -/
#guard_msgs in
#eval verdicts prefixClashPgm { Core.VerifyOptions.default with solver := "z3" }

/-! ## A datatype type parameter named like a solver sort

`Box` is uninterpreted in its parameter, so three pairwise-distinct `Box int` values
are consistent and `assert false` must fail. The parameter `Bool` must not be read as
the solver's `Bool`, under which `Box int` would have two values. -/

private def paramNamePgm :=
#strata
program Core;

datatype Box (Bool : Type) { mk(x : Bool) };

procedure R(a : Box int, b : Box int, c : Box int)
{
  assume [ne]: !(a == b) && !(a == c) && !(b == c);
  assert [param]: false;
};
#end

/-- info: param: fail -/
#guard_msgs in
#eval verdicts paramNamePgm Core.VerifyOptions.default

/-- info: param: fail -/
#guard_msgs in
#eval verdicts paramNamePgm { Core.VerifyOptions.default with solver := "z3" }

end
