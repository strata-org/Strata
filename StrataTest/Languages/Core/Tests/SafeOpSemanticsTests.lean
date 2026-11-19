/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.SMTEncoder
import StrataDDM.Integration.Lean.HashCommands

/-! # Values of the built-in operators outside their preconditions

A built-in operator means its SMT-LIB function, and each safe operator equals its plain
operator at every argument: `SafeX(args) = X(args)`. The precondition of a safe operator
only adds a well-formedness obligation at each call and marks where the operator is
expected to be used; it never changes the value. The language reference states the values
(`docs/verso/LangDefDoc.lean`, "Values outside a precondition").

These tests pin that meaning in each component that gives an operator a value:

* the concrete evaluator, which declines to evaluate a division by zero, safe or not, since
  Lean's value there differs from SMT-LIB's, and otherwise gives a safe operator its plain
  operator's value;
* the SMT encoder, through a table that classifies every preconditioned function of
  `Core.Factory`, and fails on one it does not classify;
* the solver, with one obligation per operator that states its value outside the
  precondition.
-/

meta section

namespace Core.SafeOpSemanticsTests

open Lambda

/-! ## The concrete evaluator -/

private def ev (e : Expression.Expr) : Expression.Expr :=
  (LExpr.eval 200 Core.Factory default e).1

private def bin (op a b : Expression.Expr) : Expression.Expr :=
  .app coreLoc (.app coreLoc op a) b

private def un (op a : Expression.Expr) : Expression.Expr :=
  .app coreLoc op a

private def bv (n : Nat) (v : Nat) : Expression.Expr :=
  LExpr.bitvecConst coreLoc n (BitVec.ofNat n v)

private def int (v : Int) : Expression.Expr := .intConst coreLoc v

/-- The evaluator leaves `e` as it is. -/
private def declines (e : Expression.Expr) : Bool := ev e == e

/-- The division operators of each width the tests cover, safe and plain:
    `(width, [uDiv, uMod, sDiv, sMod, safeSDiv, safeSMod])`. -/
private def bvDivOps : List (Nat × List Expression.Expr) :=
  [(1,  [bv1UDivOp,  bv1UModOp,  bv1SDivOp,  bv1SModOp,  bv1SafeSDivOp,  bv1SafeSModOp]),
   (8,  [bv8UDivOp,  bv8UModOp,  bv8SDivOp,  bv8SModOp,  bv8SafeSDivOp,  bv8SafeSModOp]),
   (32, [bv32UDivOp, bv32UModOp, bv32SDivOp, bv32SModOp, bv32SafeSDivOp, bv32SafeSModOp]),
   (64, [bv64UDivOp, bv64UModOp, bv64SDivOp, bv64SModOp, bv64SafeSDivOp, bv64SafeSModOp])]

private def intDivOps : List Expression.Expr :=
  [intDivOp, intModOp, intDivTOp, intModTOp,
   intSafeDivOp, intSafeModOp, intSafeDivTOp, intSafeModTOp]

/-! Every division operator, safe or plain, declines at a zero divisor, at every width and
for `int`: Lean's `BitVec.udiv x 0 = 0`, `Int.ediv a 0 = 0` and `Int.tdiv a 0 = 0` are not
SMT-LIB's values. -/

#guard bvDivOps.all fun (n, ops) => ops.all fun op => declines (bin op (bv n 1) (bv n 0))
#guard intDivOps.all fun op => declines (bin op (int 7) (int 0))
#guard intDivOps.all fun op => declines (bin op (int (-7)) (int 0))

/-! A nonzero divisor folds, and a safe operator folds to its plain operator's value. -/

#guard ev (bin intSafeDivOp (int 7) (int 2)) == int 3
#guard ev (bin intSafeDivTOp (int (-7)) (int 2)) == ev (bin intDivTOp (int (-7)) (int 2))
#guard ev (bin intSafeModTOp (int (-7)) (int 2)) == ev (bin intModTOp (int (-7)) (int 2))

/-! `SafeSDiv` and `SafeSMod` at `INT_MIN / -1`, outside their overflow precondition, fold to
the wrapped values `INT_MIN` and `0`, which are also those of `SDiv`, `SMod` and SMT-LIB's
`bvsdiv`, `bvsrem`. At width 1, `INT_MIN` and `-1` are both `1`. -/

private def intMin (n : Nat) : Expression.Expr := bv n (2 ^ (n - 1))
private def allOnes (n : Nat) : Expression.Expr := bv n (2 ^ n - 1)

#guard bvDivOps.all fun (n, ops) =>
  match ops with
  | [_, _, sdiv, smod, safeSDiv, safeSMod] =>
    ev (bin safeSDiv (intMin n) (allOnes n)) == intMin n &&
    ev (bin sdiv (intMin n) (allOnes n)) == intMin n &&
    ev (bin safeSMod (intMin n) (allOnes n)) == bv n 0 &&
    ev (bin smod (intMin n) (allOnes n)) == bv n 0
  | _ => false

/-! The overflow family at `bv8`: outside its precondition each safe operator folds to the
wrapped value of its plain operator. -/

#guard ev (bin bv8SafeAddOp (bv 8 127) (bv 8 1)) == bv 8 128
#guard ev (bin bv8SafeAddOp (bv 8 127) (bv 8 1)) == ev (bin bv8AddOp (bv 8 127) (bv 8 1))
#guard ev (bin bv8SafeSubOp (bv 8 128) (bv 8 1)) == ev (bin bv8SubOp (bv 8 128) (bv 8 1))
#guard ev (bin bv8SafeMulOp (bv 8 64) (bv 8 2)) == ev (bin bv8MulOp (bv 8 64) (bv 8 2))
#guard ev (un bv8SafeNegOp (bv 8 128)) == ev (un bv8NegOp (bv 8 128))
#guard ev (bin bv8SafeUAddOp (bv 8 255) (bv 8 1)) == bv 8 0
#guard ev (bin bv8SafeUSubOp (bv 8 0) (bv 8 1)) == ev (bin bv8SubOp (bv 8 0) (bv 8 1))
#guard ev (bin bv8SafeUMulOp (bv 8 16) (bv 8 16)) == ev (bin bv8MulOp (bv 8 16) (bv 8 16))
#guard ev (un bv8SafeUNegOp (bv 8 1)) == ev (un bv8NegOp (bv 8 1))

/-! ## The SMT encoder

Each preconditioned function of `Core.Factory` is classified. A safe operator is encoded as
its plain operator, which is a fixed-value SMT-LIB operator exactly where Core gives it that
value. A `Sequence` operation is not a fixed-value operator: it is encoded as a declared
function, which its axioms constrain only inside its precondition. A new preconditioned
function fails the first check until it is classified here. -/

/-- How the encoder treats a preconditioned function. -/
private inductive PrecondEncoding where
  /-- As the plain operator named. -/
  | plain (name : String)
  /-- As a declared function, not a fixed-value operator. -/
  | declared

private def bvSafePlain : List (String × String) :=
  [("SafeAdd", "Add"), ("SafeSub", "Sub"), ("SafeMul", "Mul"), ("SafeNeg", "Neg"),
   ("SafeUAdd", "Add"), ("SafeUSub", "Sub"), ("SafeUMul", "Mul"), ("SafeUNeg", "Neg"),
   ("SafeSDiv", "SDiv"), ("SafeSMod", "SMod")]

private def intSafePlain : List (String × String) :=
  [("SafeDiv", "Div"), ("SafeMod", "Mod"), ("SafeDivT", "DivT"), ("SafeModT", "ModT")]

private def declaredPrecondFuncs : List String :=
  ["Sequence.select", "Sequence.update", "Sequence.take", "Sequence.drop"]

private def classify (name : String) : Option PrecondEncoding :=
  if declaredPrecondFuncs.contains name then some .declared else
  match name.splitOn "." with
  | ["Int", op] => (intSafePlain.lookup op).map fun p => .plain s!"Int.{p}"
  | [w, op] =>
    if w.startsWith "Bv" then (bvSafePlain.lookup op).map fun p => .plain s!"{w}.{p}"
    else none
  | _ => none

private def precondFuncs : List (LFunc CoreLParams) :=
  (Core.Factory.toArray.filter (!·.preconditions.isEmpty)).toList

/-- info: [] -/
#guard_msgs in
#eval (precondFuncs.filter (classify ·.name.name |>.isNone)).map (·.name.name)

private abbrev SMTTerm := _root_.Strata.SMT.Term
private abbrev SMTType := _root_.Strata.SMT.TermType

/-- The term the encoder builds for `name` applied to `args`, if it is a built-in operator. -/
private def encodeApp (name : String) (args : List SMTTerm) (ty : SMTType) :
    Option SMTTerm :=
  (corePredefinedOpToSMTOp (CoreOp.ofString name) Core.SMT.Context.default).map
    fun (mk, _, _) => mk args ty

/-- One variable per input of `f`, all of the type of its first input (a bit vector or `int`,
    for every function `classify` maps to a plain operator), and that type. -/
private def sampleArgs (f : LFunc CoreLParams) : List SMTTerm × SMTType :=
  let ty : SMTType := match f.inputs.values.head? with
    | some (.bitvec n) => .prim (.bitvec n)
    | _ => .prim .int
  ((List.range f.inputs.length).map fun i => .var ⟨s!"x{i}", ty⟩, ty)

/-- A safe operator encodes to exactly the term of its plain operator, and a declared
    function to no built-in operator. -/
private def encodesAsClassified (f : LFunc CoreLParams) : Bool :=
  let (args, ty) := sampleArgs f
  match classify f.name.name with
  | some (.plain p) =>
    match encodeApp f.name.name args ty, encodeApp p args ty with
    | some t, some t' => t == t'
    | _, _ => false
  | some .declared => (encodeApp f.name.name args ty).isNone
  | none => false

/-- info: [] -/
#guard_msgs in
#eval (precondFuncs.filter (!encodesAsClassified ·)).map (·.name.name)

#guard precondFuncs.length == 68

end Core.SafeOpSemanticsTests

/-! ## The values, proved by the solver

Each plain operator's value outside the precondition, as SMT-LIB gives it, then each safe
operator's. Where the value is open, the tests pin what is known of it: `int.div(a, 0)` is a
function of `a` and not `0` in every model, and `int.divT(a, 0)` agrees at `a` and `-a`. For a
safe operator, its value assertion holds, and its well-formedness check fails, since the call is
outside the precondition. -/

namespace Strata

private def plainValuesPgm :=
#strata
program Core;

procedure P(x : bv W8, a : int, b : int)
{
  assert [udiv0]: bv8.uDiv(x, bv{8}(0)) == bv{8}(255);
  assert [umod0]: bv8.uMod(x, bv{8}(0)) == x;
  assert [sdiv0]: bv8.sDiv(x, bv{8}(0)) == (if bv8.sLt(x, bv{8}(0)) then bv{8}(1) else bv{8}(255));
  assert [smod0]: bv8.sMod(x, bv{8}(0)) == x;
  assert [sdivMin]: bv8.sDiv(bv{8}(128), bv{8}(255)) == bv{8}(128);
  assert [smodMin]: bv8.sMod(bv{8}(128), bv{8}(255)) == bv{8}(0);
  assert [div0Function]: a == b ==> int.div(a, 0) == int.div(b, 0);
  assert [div0Open]: int.div(a, 0) == 0;
  assert [mod0Open]: int.mod(a, 0) == a;
  assert [divT0]: int.divT(a, 0) == int.divT(int.neg(a), 0);
  assert [divT0Open]: int.divT(a, 0) == 0;
  assert [modT0]: int.modT(a, 0) == a;
};
#end

/--
info:
Obligation: udiv0
Property: assert
Result: ✅ pass

Obligation: umod0
Property: assert
Result: ✅ pass

Obligation: sdiv0
Property: assert
Result: ✅ pass

Obligation: smod0
Property: assert
Result: ✅ pass

Obligation: sdivMin
Property: assert
Result: ✅ pass

Obligation: smodMin
Property: assert
Result: ✅ pass

Obligation: div0Function
Property: assert
Result: ✅ pass

Obligation: div0Open
Property: assert
Result: ❌ fail

Obligation: mod0Open
Property: assert
Result: ❌ fail

Obligation: divT0
Property: assert
Result: ✅ pass

Obligation: divT0Open
Property: assert
Result: ❌ fail

Obligation: modT0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify plainValuesPgm (options := .quiet)

private def safeValuesPgm :=
#strata
program Core;

procedure P(x : bv W8, a : int)
{
  assert [sdiv0]: bv8.safeSDiv(x, bv{8}(0)) == bv8.sDiv(x, bv{8}(0));
  assert [smod0]: bv8.safeSMod(x, bv{8}(0)) == x;
  assert [sdivMin]: bv8.safeSDiv(bv{8}(128), bv{8}(255)) == bv{8}(128);
  assert [add]: bv8.safeAdd(bv{8}(127), bv{8}(1)) == bv{8}(128);
  assert [neg]: bv8.safeNeg(bv{8}(128)) == bv{8}(128);
  assert [uadd]: bv8.safeUAdd(bv{8}(255), bv{8}(1)) == bv{8}(0);
  assert [sub]: bv8.safeSub(bv{8}(128), bv{8}(1)) == bv{8}(127);
  assert [mul]: bv8.safeMul(bv{8}(64), bv{8}(2)) == bv{8}(128);
  assert [usub]: bv8.safeUSub(bv{8}(0), bv{8}(1)) == bv{8}(255);
  assert [umul]: bv8.safeUMul(bv{8}(16), bv{8}(16)) == bv{8}(0);
  assert [uneg]: bv8.safeUNeg(bv{8}(1)) == bv{8}(255);
  assert [div0]: int.safeDiv(a, 0) == int.div(a, 0);
  assert [mod0]: int.safeMod(a, 0) == int.mod(a, 0);
  assert [divT0]: int.safeDivT(a, 0) == int.divT(a, 0);
  assert [modT0]: int.safeModT(a, 0) == a;
};
#end

/--
info:
Obligation: assert_sdiv0_calls_Bv8.SafeSDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: assert_sdiv0_calls_Bv8.SafeSDiv_1
Property: arithmetic overflow check
Result: ✅ pass

Obligation: sdiv0
Property: assert
Result: ✅ pass

Obligation: assert_smod0_calls_Bv8.SafeSMod_0
Property: division by zero check
Result: ❌ fail

Obligation: assert_smod0_calls_Bv8.SafeSMod_1
Property: arithmetic overflow check
Result: ✅ pass

Obligation: smod0
Property: assert
Result: ✅ pass

Obligation: assert_sdivMin_calls_Bv8.SafeSDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: assert_sdivMin_calls_Bv8.SafeSDiv_1
Property: arithmetic overflow check
Result: ❌ fail

Obligation: sdivMin
Property: assert
Result: ✅ pass

Obligation: assert_add_calls_Bv8.SafeAdd_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: add
Property: assert
Result: ✅ pass

Obligation: assert_neg_calls_Bv8.SafeNeg_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: neg
Property: assert
Result: ✅ pass

Obligation: assert_uadd_calls_Bv8.SafeUAdd_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: uadd
Property: assert
Result: ✅ pass

Obligation: assert_sub_calls_Bv8.SafeSub_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: sub
Property: assert
Result: ✅ pass

Obligation: assert_mul_calls_Bv8.SafeMul_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: mul
Property: assert
Result: ✅ pass

Obligation: assert_usub_calls_Bv8.SafeUSub_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: usub
Property: assert
Result: ✅ pass

Obligation: assert_umul_calls_Bv8.SafeUMul_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: umul
Property: assert
Result: ✅ pass

Obligation: assert_uneg_calls_Bv8.SafeUNeg_0
Property: arithmetic overflow check
Result: ❌ fail

Obligation: uneg
Property: assert
Result: ✅ pass

Obligation: assert_div0_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: div0
Property: assert
Result: ✅ pass

Obligation: assert_mod0_calls_Int.SafeMod_0
Property: division by zero check
Result: ❌ fail

Obligation: mod0
Property: assert
Result: ✅ pass

Obligation: assert_divT0_calls_Int.SafeDivT_0
Property: division by zero check
Result: ❌ fail

Obligation: divT0
Property: assert
Result: ✅ pass

Obligation: assert_modT0_calls_Int.SafeModT_0
Property: division by zero check
Result: ❌ fail

Obligation: modT0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify safeValuesPgm (options := .quiet)

/-! ## Verdicts

An axiom that fixes a division at an unconstrained divisor does not imply that the divisor is
nonzero: `int.div(10, 0)` is unspecified, so it may be `5`. -/

private def axiomDivPgm :=
#strata
program Core;

const c : int;
axiom [d]: int.safeDiv(10, c) == 5;

procedure P()
{
  assert [nz]: !(c == 0);
};
#end

/--
info:
Obligation: nz
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify axiomDivPgm (options := .quiet)

/-! A destructor applied to the wrong constructor, in an axiom: `Option..val(None())` is a
value of the element type, so the axiom states nothing false and the program verifies. -/

private def axiomWrongDestructorPgm :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(val: a) };
axiom [p]: Option..val(None()) == 5;

procedure P()
{
  assert [t]: true;
};
#end

/--
info:
Obligation: t
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify axiomWrongDestructorPgm (options := .quiet)

/-! With an element type that nothing fixes, type checking rejects the axiom before any
value is given to it. -/

private def axiomFreeElementTypePgm :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(val: a) };
axiom [p]: Option..val(None()) == Option..val(None());

procedure P()
{
  assert [t]: true;
};
#end

/--
error: ❌ Type checking error.
Axiom 'p' is typed at a generated type variable that is not declared
-/
#guard_msgs in
#eval Core.verify axiomFreeElementTypePgm (options := .quiet)

/-! A guarded axiom keeps its meaning inside its guard: with `c == 2`, the division and its
well-formedness check both hold. -/

private def guardedAxiomPgm :=
#strata
program Core;

const c : int;
axiom [g]: c != 0 ==> int.safeDiv(10, c) == 5;

procedure P()
  spec {
    requires [two]: c == 2;
  }
{
  assert [five]: int.safeDiv(10, c) == 5;
};
#end

/--
info:
Obligation: assert_five_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: five
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardedAxiomPgm (options := .quiet)

/-! A bitvector division by zero has SMT-LIB's value, all ones. -/

private def bvDivZeroPgm :=
#strata
program Core;

procedure P(x : bv W8)
  spec {
    requires [zero]: x == bv{8}(0);
  }
{
  assert [allOnes]: bv8.uDiv(bv{8}(1), x) == bv{8}(255);
};
#end

/--
info:
Obligation: allOnes
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify bvDivZeroPgm (options := .quiet)

end Strata
end
