/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Languages.Core.Tests.StringEvalAgreementTest

/-! # Core's evaluators of integers, bitvectors, datatypes, maps and sequences agree with cvc5

`StringEvalAgreementTest.lean` checks that Core's evaluator and cvc5 decide lemmas over
strings alike: each lemma is verified on literals, which Core's evaluator folds, and on
parameters assumed equal to those literals, which cvc5 decides. This file uses the same
machinery for the other values Core's evaluator computes with: integers (the two rounding
conventions of division and remainder), bitvectors (wrapping arithmetic, division, bitwise
operators, comparisons, shifts, overflow predicates, conversions to and from integers),
datatypes (testers, selectors and equality of constructor terms), maps and sequences (their
operations on literals). A lemma's
arguments are typed Core literals, and a list of lemmas may need declarations first (the
datatypes), which `check` takes as a prelude.

Each line prints both verdicts and who reached them, as in the string test: `evaluator`
when no query reached the solver, `cvc5` when one did. A line ending in `DISAGREE` is a
lemma the two decide differently. Only one kind is expected: the evaluator passes and cvc5
answers unknown, an incompleteness of the solver (the map and sequence equalities below). A
line where one side passes and the other fails means one of them is wrong: it is a bug to
fix, never output to pin. A lemma the evaluator does not fold (a division by zero,
a selector of the wrong constructor) reaches cvc5 on both sides; such lines show where
Core leaves a term to the solver.

Sets are not here: Core's evaluator has no rules for their operations (they have no
`concreteEval` in `Core.Factory`), so both sides of such a lemma would reach the solver,
and there would be nothing to compare. -/

meta section
open Strata

namespace Core.CoreEvalAgreementTest

open Core.StringEvalAgreementTest (Case verdicts comparison who)

/-! ## Typed lemmas -/

/-- An argument of a lemma: its Core type and a literal of that type. -/
private structure Arg where
  ty : String
  lit : String
  deriving Inhabited

/-- The integer `n` as an argument: a negative one is `int.neg(-n)`. -/
private def int (n : Int) : Arg := ⟨"int", if n < 0 then s!"int.neg({-n})" else toString n⟩

/-- The 8-bit bitvector `n` as an argument. -/
private def bv8 (n : Nat) : Arg := ⟨"bv W8", s!"bv\{8}({n})"⟩

/-- A lemma over typed arguments: `$i` in `goal` stands for the `i`-th argument. -/
private structure TypedCase where
  name : String
  goal : String
  args : List Arg

/-- `c` with its arguments' literals, for `Case.render`. -/
private def TypedCase.toCase (c : TypedCase) : Case := ⟨c.name, c.goal, c.args.map (·.lit)⟩

/-- A procedure that asserts `c` on literals. -/
private def TypedCase.onLiterals (c : TypedCase) : String :=
  s!"procedure {c.name}_literals()\n\{\n  assert [{c.name}]: \
    {c.toCase.render fun i => (c.args.getD i default).lit};\n};\n"

/-- A procedure that asserts `c` on parameters assumed equal to its literals. -/
private def TypedCase.onParameters (c : TypedCase) : String :=
  let params := ", ".intercalate (c.args.zipIdx.map fun (a, i) => s!"a{i} : {a.ty}")
  let assumes := String.join <| c.args.zipIdx.map fun (a, i) => s!"  assume a{i} == {a.lit};\n"
  s!"procedure {c.name}_parameters({params})\n\{\n{assumes}  assert [{c.name}]: \
    {c.toCase.render (s!"a{·}")};\n};\n"

/-- Verify each case on literals and on parameters, after `prelude`, and print both verdicts
    and who reached them. Fails if a parameter lemma did not reach the solver: the pipeline
    would then have folded it with the assumed equalities, and the case would compare the
    evaluator with itself. -/
private def check (cases : List TypedCase) (prelude : String := "") : IO Unit := do
  let onLiterals ← verdicts (prelude ++ String.join (cases.map TypedCase.onLiterals))
  let onParameters ← verdicts (prelude ++ String.join (cases.map TypedCase.onParameters))
  for c in cases do
    match onLiterals.lookup c.name, onParameters.lookup c.name with
    | some (l, ls), some (p, ps) =>
      unless ps do
        throw (IO.userError s!"{c.name}: the parameter lemma did not reach the solver")
      IO.println s!"{c.name}: {who ls} {l}, {who ps} {p}{comparison l p}"
    | _, _ => IO.println s!"{c.name}: missing obligation"

/-! ## Integer division and remainder

`int.div` and `int.mod` round as SMT-LIB's `div` and `mod` do (the remainder is never
negative); `int.divT` and `int.modT` truncate toward zero. The two differ exactly when an
operand is negative, so the cases take every sign. Division by zero is not reduced, and is
unspecified in SMT-LIB, so cvc5 decides both sides of `div_by_zero`, and finds a
counterexample to each. -/

/--
info: div_neg_pos: evaluator ✅ pass, cvc5 ✅ pass
mod_neg_pos: evaluator ✅ pass, cvc5 ✅ pass
div_pos_neg: evaluator ✅ pass, cvc5 ✅ pass
mod_pos_neg: evaluator ✅ pass, cvc5 ✅ pass
div_neg_neg: evaluator ✅ pass, cvc5 ✅ pass
mod_neg_neg: evaluator ✅ pass, cvc5 ✅ pass
divT_neg_pos: evaluator ✅ pass, cvc5 ✅ pass
modT_neg_pos: evaluator ✅ pass, cvc5 ✅ pass
divT_pos_neg: evaluator ✅ pass, cvc5 ✅ pass
modT_pos_neg: evaluator ✅ pass, cvc5 ✅ pass
divT_neg_neg: evaluator ✅ pass, cvc5 ✅ pass
modT_neg_neg: evaluator ✅ pass, cvc5 ✅ pass
div_by_zero: cvc5 ❌ fail, cvc5 ❌ fail
-/
#guard_msgs in
#eval check [
  ⟨"div_neg_pos", "int.div($0, $1) == $2", [int (-7), int 2, int (-4)]⟩,
  ⟨"mod_neg_pos", "int.mod($0, $1) == $2", [int (-7), int 2, int 1]⟩,
  ⟨"div_pos_neg", "int.div($0, $1) == $2", [int 7, int (-2), int (-3)]⟩,
  ⟨"mod_pos_neg", "int.mod($0, $1) == $2", [int 7, int (-2), int 1]⟩,
  ⟨"div_neg_neg", "int.div($0, $1) == $2", [int (-7), int (-2), int 4]⟩,
  ⟨"mod_neg_neg", "int.mod($0, $1) == $2", [int (-7), int (-2), int 1]⟩,
  ⟨"divT_neg_pos", "int.divT($0, $1) == $2", [int (-7), int 2, int (-3)]⟩,
  ⟨"modT_neg_pos", "int.modT($0, $1) == $2", [int (-7), int 2, int (-1)]⟩,
  ⟨"divT_pos_neg", "int.divT($0, $1) == $2", [int 7, int (-2), int (-3)]⟩,
  ⟨"modT_pos_neg", "int.modT($0, $1) == $2", [int 7, int (-2), int 1]⟩,
  ⟨"divT_neg_neg", "int.divT($0, $1) == $2", [int (-7), int (-2), int 3]⟩,
  ⟨"modT_neg_neg", "int.modT($0, $1) == $2", [int (-7), int (-2), int (-1)]⟩,
  ⟨"div_by_zero", "int.div($0, $1) == $2", [int 7, int 0, int 0]⟩]

/-! ## Bitvectors

Core's evaluator folds 8-bit operations on literals, wrapping as SMT-LIB does, except two
kinds that it leaves to the solver, which then decides both sides: division and remainder
by zero (SMT-LIB defines `bvudiv x 0` as all ones and `bvurem x 0` as `x`, and signed
division from them: `bvsdiv x 0` is 1 for a negative `x`), and shifts by the width or more
(zero, or the sign bit repeated). `sMod` is SMT-LIB's `bvsrem`, whose sign
is the dividend's (`smod_pos_neg` gives 1, where `bvsmod` would give -1). Each comparison
takes its arguments in an order where swapping them changes the answer. The overflow
predicates are Core's own operators; the SMT encoder spells each out, so these cases check
those encodings too. -/

/--
info: add_wraps: evaluator ✅ pass, cvc5 ✅ pass
sub_wraps: evaluator ✅ pass, cvc5 ✅ pass
mul_wraps: evaluator ✅ pass, cvc5 ✅ pass
neg_min: evaluator ✅ pass, cvc5 ✅ pass
udiv: evaluator ✅ pass, cvc5 ✅ pass
umod: evaluator ✅ pass, cvc5 ✅ pass
sdiv_neg: evaluator ✅ pass, cvc5 ✅ pass
sdiv_min_by_minus_one: evaluator ✅ pass, cvc5 ✅ pass
smod_neg_pos: evaluator ✅ pass, cvc5 ✅ pass
smod_pos_neg: evaluator ✅ pass, cvc5 ✅ pass
udiv_by_zero: cvc5 ✅ pass, cvc5 ✅ pass
umod_by_zero: cvc5 ✅ pass, cvc5 ✅ pass
shl: evaluator ✅ pass, cvc5 ✅ pass
ushr: evaluator ✅ pass, cvc5 ✅ pass
sshr: evaluator ✅ pass, cvc5 ✅ pass
shl_by_width: cvc5 ✅ pass, cvc5 ✅ pass
ushr_by_width: cvc5 ✅ pass, cvc5 ✅ pass
sshr_by_width: cvc5 ✅ pass, cvc5 ✅ pass
sadd_overflow: evaluator ✅ pass, cvc5 ✅ pass
ssub_overflow: evaluator ✅ pass, cvc5 ✅ pass
smul_overflow: evaluator ✅ pass, cvc5 ✅ pass
smul_no_overflow: evaluator ✅ pass, cvc5 ✅ pass
sdiv_overflow: evaluator ✅ pass, cvc5 ✅ pass
sneg_overflow: evaluator ✅ pass, cvc5 ✅ pass
uadd_overflow: evaluator ✅ pass, cvc5 ✅ pass
usub_overflow: evaluator ✅ pass, cvc5 ✅ pass
umul_overflow: evaluator ✅ pass, cvc5 ✅ pass
uneg_overflow: evaluator ✅ pass, cvc5 ✅ pass
and: evaluator ✅ pass, cvc5 ✅ pass
or: evaluator ✅ pass, cvc5 ✅ pass
xor: evaluator ✅ pass, cvc5 ✅ pass
not: evaluator ✅ pass, cvc5 ✅ pass
ult: evaluator ✅ pass, cvc5 ✅ pass
ule: evaluator ✅ pass, cvc5 ✅ pass
ugt: evaluator ✅ pass, cvc5 ✅ pass
uge: evaluator ✅ pass, cvc5 ✅ pass
slt: evaluator ✅ pass, cvc5 ✅ pass
sle: evaluator ✅ pass, cvc5 ✅ pass
sgt: evaluator ✅ pass, cvc5 ✅ pass
sge: evaluator ✅ pass, cvc5 ✅ pass
sdiv_by_zero: cvc5 ✅ pass, cvc5 ✅ pass
to_int: evaluator ✅ pass, cvc5 ✅ pass
to_uint: evaluator ✅ pass, cvc5 ✅ pass
of_int: evaluator ✅ pass, cvc5 ✅ pass
safe_add: evaluator ✅ pass, cvc5 ✅ pass
safe_uadd: evaluator ✅ pass, cvc5 ✅ pass
-/
#guard_msgs in
#eval check [
  ⟨"add_wraps", "bv8.add($0, $1) == $2", [bv8 255, bv8 1, bv8 0]⟩,
  ⟨"sub_wraps", "bv8.sub($0, $1) == $2", [bv8 0, bv8 1, bv8 255]⟩,
  ⟨"mul_wraps", "bv8.mul($0, $1) == $2", [bv8 16, bv8 16, bv8 0]⟩,
  ⟨"neg_min", "bv8.neg($0) == $0", [bv8 128]⟩,
  ⟨"udiv", "bv8.uDiv($0, $1) == $2", [bv8 200, bv8 7, bv8 28]⟩,
  ⟨"umod", "bv8.uMod($0, $1) == $2", [bv8 200, bv8 7, bv8 4]⟩,
  ⟨"sdiv_neg", "bv8.sDiv($0, $1) == $2", [bv8 249, bv8 2, bv8 253]⟩,
  ⟨"sdiv_min_by_minus_one", "bv8.sDiv($0, $1) == $0", [bv8 128, bv8 255]⟩,
  ⟨"smod_neg_pos", "bv8.sMod($0, $1) == $2", [bv8 249, bv8 2, bv8 255]⟩,
  ⟨"smod_pos_neg", "bv8.sMod($0, $1) == $2", [bv8 7, bv8 254, bv8 1]⟩,
  ⟨"udiv_by_zero", "bv8.uDiv($0, $1) == $2", [bv8 7, bv8 0, bv8 255]⟩,
  ⟨"umod_by_zero", "bv8.uMod($0, $1) == $0", [bv8 7, bv8 0]⟩,
  ⟨"shl", "bv8.shl($0, $1) == $2", [bv8 3, bv8 6, bv8 192]⟩,
  ⟨"ushr", "bv8.uShr($0, $1) == $2", [bv8 200, bv8 3, bv8 25]⟩,
  ⟨"sshr", "bv8.sShr($0, $1) == $2", [bv8 200, bv8 3, bv8 249]⟩,
  ⟨"shl_by_width", "bv8.shl($0, $1) == $2", [bv8 1, bv8 8, bv8 0]⟩,
  ⟨"ushr_by_width", "bv8.uShr($0, $1) == $2", [bv8 128, bv8 9, bv8 0]⟩,
  ⟨"sshr_by_width", "bv8.sShr($0, $1) == $2", [bv8 128, bv8 9, bv8 255]⟩,
  ⟨"sadd_overflow", "bv8.sAddOverflow($0, $1)", [bv8 127, bv8 1]⟩,
  ⟨"ssub_overflow", "bv8.sSubOverflow($0, $1)", [bv8 128, bv8 1]⟩,
  ⟨"smul_overflow", "bv8.sMulOverflow($0, $1)", [bv8 16, bv8 8]⟩,
  ⟨"smul_no_overflow", "!bv8.sMulOverflow($0, $1)", [bv8 255, bv8 127]⟩,
  ⟨"sdiv_overflow", "bv8.sDivOverflow($0, $1)", [bv8 128, bv8 255]⟩,
  ⟨"sneg_overflow", "bv8.sNegOverflow($0)", [bv8 128]⟩,
  ⟨"uadd_overflow", "bv8.uAddOverflow($0, $1)", [bv8 255, bv8 1]⟩,
  ⟨"usub_overflow", "bv8.uSubOverflow($0, $1)", [bv8 0, bv8 1]⟩,
  ⟨"umul_overflow", "bv8.uMulOverflow($0, $1)", [bv8 16, bv8 16]⟩,
  ⟨"uneg_overflow", "bv8.uNegOverflow($0)", [bv8 1]⟩,
  ⟨"and", "bv8.and($0, $1) == $2", [bv8 240, bv8 60, bv8 48]⟩,
  ⟨"or", "bv8.or($0, $1) == $2", [bv8 240, bv8 15, bv8 255]⟩,
  ⟨"xor", "bv8.xor($0, $1) == $2", [bv8 255, bv8 15, bv8 240]⟩,
  ⟨"not", "bv8.not($0) == $1", [bv8 15, bv8 240]⟩,
  ⟨"ult", "bv8.uLt($0, $1)", [bv8 1, bv8 200]⟩,
  ⟨"ule", "bv8.uLe($0, $1)", [bv8 1, bv8 200]⟩,
  ⟨"ugt", "bv8.uGt($0, $1)", [bv8 200, bv8 1]⟩,
  ⟨"uge", "bv8.uGe($0, $1)", [bv8 200, bv8 1]⟩,
  ⟨"slt", "bv8.sLt($0, $1)", [bv8 200, bv8 1]⟩,
  ⟨"sle", "bv8.sLe($0, $1)", [bv8 200, bv8 1]⟩,
  ⟨"sgt", "bv8.sGt($0, $1)", [bv8 1, bv8 200]⟩,
  ⟨"sge", "bv8.sGe($0, $1)", [bv8 1, bv8 200]⟩,
  ⟨"sdiv_by_zero", "bv8.sDiv($0, $1) == $2", [bv8 249, bv8 0, bv8 1]⟩,
  ⟨"to_int", "bv8.toInt($0) == int.neg(1)", [bv8 255]⟩,
  ⟨"to_uint", "bv8.toUInt($0) == 255", [bv8 255]⟩,
  ⟨"of_int", "as_bv8($0) == $1", [int (-1), bv8 255]⟩,
  ⟨"safe_add", "bv8.safeAdd($0, $1) == $2", [bv8 100, bv8 27, bv8 127]⟩,
  ⟨"safe_uadd", "bv8.safeUAdd($0, $1) == $2", [bv8 200, bv8 55, bv8 255]⟩]

/-! ## Datatypes

Constructor terms are values; Core's evaluator applies selectors to them, evaluates testers
(through their bodies, which use the datatype's eliminator), and decides equality of two
constructor terms. A selector of the wrong constructor is not reduced, and Core adds a
precondition obligation for it (`hd_of_nil`), which fails during evaluation: the first
lines of the output. -/

/-- The datatypes of the cases below. -/
private def datatypes : String :=
  "datatype IntList { Nil(), Cons(hd : int, tl : IntList) };\n\
   datatype Tree { Leaf(), Node(left : Tree, val : int, right : Tree) };\n"

/-- A list or tree literal as an argument. -/
private def list (lit : String) : Arg := ⟨"IntList", lit⟩
private def tree (lit : String) : Arg := ⟨"Tree", lit⟩

/--
info:

Obligation assert_hd_of_nil_calls_IntList..hd_0: failed!

Result obtained during evaluation.
hd: evaluator ✅ pass, cvc5 ✅ pass
tl: evaluator ✅ pass, cvc5 ✅ pass
hd_of_tl: evaluator ✅ pass, cvc5 ✅ pass
is_cons: evaluator ✅ pass, cvc5 ✅ pass
is_nil_not: evaluator ✅ pass, cvc5 ✅ pass
eq_same: evaluator ✅ pass, cvc5 ✅ pass
eq_diff_field: evaluator ✅ pass, cvc5 ✅ pass
eq_diff_constr: evaluator ✅ pass, cvc5 ✅ pass
tree_val: evaluator ✅ pass, cvc5 ✅ pass
tree_is_leaf: evaluator ✅ pass, cvc5 ✅ pass
ite_on_tester: evaluator ✅ pass, cvc5 ✅ pass
hd_of_nil: cvc5 ❌ fail, cvc5 ❌ fail
-/
#guard_msgs in
#eval check (prelude := datatypes) [
  ⟨"hd", "IntList..hd($0) == 1", [list "Cons(1, Nil())"]⟩,
  ⟨"tl", "IntList..tl($0) == Nil()", [list "Cons(1, Nil())"]⟩,
  ⟨"hd_of_tl", "IntList..hd(IntList..tl($0)) == 2", [list "Cons(1, Cons(2, Nil()))"]⟩,
  ⟨"is_cons", "IntList..isCons($0)", [list "Cons(1, Nil())"]⟩,
  ⟨"is_nil_not", "!IntList..isNil($0)", [list "Cons(1, Nil())"]⟩,
  ⟨"eq_same", "$0 == $1", [list "Cons(1, Cons(2, Nil()))", list "Cons(1, Cons(2, Nil()))"]⟩,
  ⟨"eq_diff_field", "!($0 == $1)", [list "Cons(1, Nil())", list "Cons(2, Nil())"]⟩,
  ⟨"eq_diff_constr", "!($0 == $1)", [list "Cons(1, Nil())", list "Nil()"]⟩,
  ⟨"tree_val", "Tree..val(Tree..right($0)) == 6",
    [tree "Node(Leaf(), 5, Node(Leaf(), 6, Leaf()))"]⟩,
  ⟨"tree_is_leaf", "Tree..isLeaf(Tree..left($0))", [tree "Node(Leaf(), 5, Leaf())"]⟩,
  ⟨"ite_on_tester", "(if Tree..isNode($0) then Tree..val($0) else 0) == 5",
    [tree "Node(Leaf(), 5, Leaf())"]⟩,
  ⟨"hd_of_nil", "IntList..hd($0) == 0", [list "Nil()"]⟩]

/-! ## Maps and sequences

Core's evaluator folds the operations of `Map` and `Sequence` on literals: `mapConst`, a
read, an update (which drops an entry set to the map's default), and the sequence
operations in bounds. It also decides the equality of two equal literals, but decides
neither the equality nor the disequality of two different map literals, which may denote
the same map.

Two lemmas print `DISAGREE`, both with `pass` for the evaluator and `unknown` for cvc5:
`map_eq_default_dropped`, where updating the one entry to the default gives back the empty
map, and `seq_eq`, where appending two one-element sequences gives the two-element one.
Both lemmas are true, as Core's semantics takes a map to be a function and a sequence a
list, so the evaluator is right and the solver is incomplete: by default the SMT encoding
axiomatizes maps and sequences without extensionality. With `useArrayTheory`, maps are SMT
arrays, which are extensional; there is no such option for sequences. The disagreement
makes such a lemma proved or unknown depending on whether the evaluator reaches it first;
neither answer is wrong. Three more lemmas are unknown on both sides: the equality of two
map literals built in different orders, the disequality of two different maps, which the
evaluator leaves undecided, and a read out of bounds, which it does not fold. -/

/-- A map or sequence term as an argument; Core's evaluator folds it to a literal. -/
private def intMap (lit : String) : Arg := ⟨"Map int int", lit⟩
private def intSeq (lit : String) : Arg := ⟨"Sequence int", lit⟩

/-- The sequences `[1]`, `[2]` and `[1, 2]`. -/
private def seq1 := "Sequence.build(Sequence.empty<int>(), 1)"
private def seq2 := "Sequence.build(Sequence.empty<int>(), 2)"
private def seq12 := s!"Sequence.build({seq1}, 2)"

/--
info: select_hit: evaluator ✅ pass, cvc5 ✅ pass
select_default: evaluator ✅ pass, cvc5 ✅ pass
select_const: evaluator ✅ pass, cvc5 ✅ pass
update_again: evaluator ✅ pass, cvc5 ✅ pass
update_other: evaluator ✅ pass, cvc5 ✅ pass
update_to_default: evaluator ✅ pass, cvc5 ✅ pass
map_eq_same: evaluator ✅ pass, cvc5 ✅ pass
map_eq_reordered: cvc5 ❓ unknown, cvc5 ❓ unknown
map_eq_default_dropped: evaluator ✅ pass, cvc5 ❓ unknown DISAGREE
map_neq: cvc5 ❓ unknown, cvc5 ❓ unknown
seq_length: evaluator ✅ pass, cvc5 ✅ pass
seq_select: evaluator ✅ pass, cvc5 ✅ pass
seq_select_out: cvc5 ❓ unknown, cvc5 ❓ unknown
seq_append: evaluator ✅ pass, cvc5 ✅ pass
seq_contains: evaluator ✅ pass, cvc5 ✅ pass
seq_contains_not: evaluator ✅ pass, cvc5 ✅ pass
seq_take: evaluator ✅ pass, cvc5 ✅ pass
seq_drop: evaluator ✅ pass, cvc5 ✅ pass
seq_update: evaluator ✅ pass, cvc5 ✅ pass
seq_eq: evaluator ✅ pass, cvc5 ❓ unknown DISAGREE
-/
#guard_msgs in
#eval check [
  ⟨"select_hit", "$0[1] == 10", [intMap "mapConst<int>(0)[1 := 10]"]⟩,
  ⟨"select_default", "$0[2] == 0", [intMap "mapConst<int>(0)[1 := 10]"]⟩,
  ⟨"select_const", "$0[5] == 7", [intMap "mapConst<int>(7)"]⟩,
  ⟨"update_again", "$0[1 := 30][1] == 30", [intMap "mapConst<int>(0)[1 := 10][2 := 20]"]⟩,
  ⟨"update_other", "$0[1 := 30][2] == 20", [intMap "mapConst<int>(0)[1 := 10][2 := 20]"]⟩,
  ⟨"update_to_default", "$0[1 := 0][1] == 0", [intMap "mapConst<int>(0)[1 := 10]"]⟩,
  ⟨"map_eq_same", "$0 == $1",
    [intMap "mapConst<int>(0)[1 := 10]", intMap "mapConst<int>(0)[1 := 10]"]⟩,
  ⟨"map_eq_reordered", "$0 == $1",
    [intMap "mapConst<int>(0)[1 := 10][2 := 20]", intMap "mapConst<int>(0)[2 := 20][1 := 10]"]⟩,
  ⟨"map_eq_default_dropped", "$0[1 := 0] == $1",
    [intMap "mapConst<int>(0)[1 := 10]", intMap "mapConst<int>(0)"]⟩,
  ⟨"map_neq", "!($0 == $1)",
    [intMap "mapConst<int>(0)[1 := 10]", intMap "mapConst<int>(0)[1 := 20]"]⟩,
  ⟨"seq_length", "Sequence.length($0) == 2", [intSeq seq12]⟩,
  ⟨"seq_select", "Sequence.select($0, 1) == 2", [intSeq seq12]⟩,
  ⟨"seq_select_out", "Sequence.select($0, 2) == 0", [intSeq seq12]⟩,
  ⟨"seq_append", "Sequence.length(Sequence.append($0, $0)) == 4", [intSeq seq12]⟩,
  ⟨"seq_contains", "Sequence.contains($0, 2)", [intSeq seq12]⟩,
  ⟨"seq_contains_not", "!Sequence.contains($0, 3)", [intSeq seq12]⟩,
  ⟨"seq_take", "Sequence.length(Sequence.take($0, 1)) == 1", [intSeq seq12]⟩,
  ⟨"seq_drop", "Sequence.select(Sequence.drop($0, 1), 0) == 2", [intSeq seq12]⟩,
  ⟨"seq_update", "Sequence.select(Sequence.update($0, 0, 5), 0) == 5", [intSeq seq12]⟩,
  ⟨"seq_eq", "Sequence.append($0, $1) == $2", [intSeq seq1, intSeq seq2, intSeq seq12]⟩]

end Core.CoreEvalAgreementTest

end
