/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CoreMatch.Verify
import Strata.Languages.CoreMatch.DDMTransform.StrataGen

/-!
End-to-end source pipeline tests. Each program travels DDM parse →
typed AST → `MProgram` → `Core.Program` and is asserted on for
structural invariants in the lowered Core (eliminator-headed
function bodies, no self-references after natural-style rewrite,
ite-shaped procedure bodies) and for the diagnostic surface of the
redundancy and non-structural checks.
-/

open Strata Lambda

namespace CoreMatchSourceTest


/-! Inspection helpers -/

private partial def headOpName
    (e : LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩) : Option String :=
  match e with
  | .app _ f _      => headOpName f
  | .op _ ⟨n, _⟩ _  => some n
  | _ => none

private partial def hasFvar
    (e : LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩) (name : String) : Bool :=
  match e with
  | .fvar _ ⟨n, _⟩ _   => n == name
  | .app _ f a         => hasFvar f name || hasFvar a name
  | .abs _ _ _ b       => hasFvar b name
  | .quant _ _ _ _ t b => hasFvar t name || hasFvar b name
  | .ite _ c t f       => hasFvar c name || hasFvar t name || hasFvar f name
  | .eq _ a b          => hasFvar a name || hasFvar b name
  | _ => false

private partial def opNames
    (e : LExpr ⟨⟨Unit, Unit⟩, LMonoTy⟩) : List String :=
  match e with
  | .op _ ⟨n, _⟩ _     => [n]
  | .app _ f a         => opNames f ++ opNames a
  | .abs _ _ _ b       => opNames b
  | .quant _ _ _ _ t b => opNames t ++ opNames b
  | .ite _ c t f       => opNames c ++ opNames t ++ opNames f
  | .eq _ a b          => opNames a ++ opNames b
  | _ => []

private def parseToCore (p : Strata.Program)
    : Except DiagnosticModel Core.Program :=
  Strata.CoreMatch.Verify.parseToCore p "test"

private def lookupFn (p : Strata.Program) (name : String) : Option Core.Function :=
  match parseToCore p with
  | .error _ => none
  | .ok prog =>
    prog.decls.findSome? fun
      | .func f _ => if f.name.name == name then some f else none
      | _ => none

private def lookupProc (p : Strata.Program) (name : String) : Option Core.Procedure :=
  match parseToCore p with
  | .error _ => none
  | .ok prog =>
    prog.decls.findSome? fun
      | .proc d _ => if d.header.name.name == name then some d else none
      | _ => none

private def declCount (p : Strata.Program) : Nat :=
  match parseToCore p with
  | .ok prog => prog.decls.length
  | .error _ => 0

private def parseError? (p : Strata.Program) : Bool :=
  match parseToCore p with
  | .ok _    => false
  | .error _ => true

/-- Body is `D$Elim …`, no self-reference left, no termination
    obligation: the catamorphism convention. -/
private def isCataFn (dtName : String) (f : Core.Function) : Bool :=
  match f.body with
  | none => false
  | some b =>
    headOpName b == some (dtName ++ "$Elim")
    && !hasFvar b f.name.name
    && f.preconditions.isEmpty
    && f.axioms.isEmpty
    && f.attr.isEmpty

/-- Procedure body lowered to a single ite (possibly wrapped in a
    block), as a match-statement should produce. -/
private def isIteHeadedProc (d : Core.Procedure) : Bool :=
  match d.body with
  | [.block _ [.ite _ _ _ _] _] => true
  | [.ite _ _ _ _]              => true
  | _ => false


/-! Non-recursive enum (option-like) -/

private def pOption : Strata.Program :=
#strata
program CoreMatch;

datatype OptInt () { None(), Some(val : int) };

function getOr(o : OptInt, dflt : int) : int
{
  match o {
    arm None()              => dflt;
    arm Some(val : int)     => val;
  }
};

function isSome(o : OptInt) : bool
{
  match o {
    arm None()              => false;
    arm Some(val : int)     => true;
  }
};
#end

#guard declCount pOption == 5

#guard match lookupFn pOption "getOr" with
       | some f => headOpName f.body.get! == some "OptInt$Elim"
       | none => false

#guard match lookupFn pOption "isSome" with
       | some f => headOpName f.body.get! == some "OptInt$Elim"
       | none => false


/-! Pure enum with wildcard arms -/

private def pEnum : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue(), Yellow() };

function isWarm(c : Color) : bool
{
  match c {
    arm Red()    => true;
    arm Yellow() => true;
    arm _        => false;
  }
};

function rank(c : Color) : int
{
  match c {
    arm Red()    => 1;
    arm Green()  => 2;
    arm Blue()   => 3;
    arm Yellow() => 4;
  }
};
#end

#guard declCount pEnum == 5

-- Both functions lower to Color$Elim head.
#guard match lookupFn pEnum "isWarm" with
       | some f => headOpName f.body.get! == some "Color$Elim"
       | none => false

#guard match lookupFn pEnum "rank" with
       | some f => headOpName f.body.get! == some "Color$Elim"
       | none => false


/-! Unary recursion (Peano natural numbers) -/

private def pPeano : Strata.Program :=
#strata
program CoreMatch;

datatype Nat () { Zero(), Succ(pred : Nat) };

rec function toInt(n : Nat) : int
{
  match n {
    arm Zero()           => 0;
    arm Succ(pred : Nat) => 1 + toInt(pred);
  }
};

rec function isZero(n : Nat) : bool
{
  match n {
    arm Zero()           => true;
    arm Succ(pred : Nat) => false;
  }
};
#end

-- toInt: cata invariants hold.
#guard match lookupFn pPeano "toInt" with
       | some f => isCataFn "Nat" f
       | none => false

-- isZero: doesn't actually recurse (the Succ arm returns false), but
-- the body is still eliminator-headed.
#guard match lookupFn pPeano "isZero" with
       | some f => headOpName f.body.get! == some "Nat$Elim"
       | none => false


/-! Binary-tree DFS (multiple recursive fields) -/

private def pTree : Strata.Program :=
#strata
program CoreMatch;

datatype Tree () { Leaf(), Node(value : int, left : Tree, right : Tree) };

rec function treeSum(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      value + treeSum(left) + treeSum(right);
  }
};

rec function nodeCount(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      1 + nodeCount(left) + nodeCount(right);
  }
};
#end

#guard match lookupFn pTree "treeSum" with
       | some f => isCataFn "Tree" f
       | none => false

#guard match lookupFn pTree "nodeCount" with
       | some f => isCataFn "Tree" f
       | none => false

-- The only ops appearing in `treeSum`'s body should be `Tree$Elim`
-- and `Int.Add` — no `treeSum` reference at all, confirming the
-- natural-style rewrite consumed both `treeSum(left)` and
-- `treeSum(right)`.
#guard match lookupFn pTree "treeSum" with
       | some f =>
         match f.body with
         | some b => (opNames b).all fun n => n == "Tree$Elim" || n == "Int.Add"
         | none => false
       | none => false


/-! Mutually recursive functions -/

private def pMutual : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function length(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + length(tl);
  }
};

rec function sum(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => hd + sum(tl);
  }
};
#end

#guard match lookupFn pMutual "length" with
       | some f => isCataFn "List" f
       | none => false

#guard match lookupFn pMutual "sum" with
       | some f => isCataFn "List" f
       | none => false


/-! Heterogeneous constructor field types -/

private def pEither : Strata.Program :=
#strata
program CoreMatch;

datatype Either () { LeftI(v : int), RightB(b : bool) };

function isError(e : Either) : bool
{
  match e {
    arm LeftI(v : int)   => v < 0;
    arm RightB(b : bool) => !b;
  }
};

function describeKind(e : Either) : int
{
  match e {
    arm LeftI(v : int)   => 1;
    arm RightB(b : bool) => 2;
  }
};
#end

#guard match lookupFn pEither "isError" with
       | some f => headOpName f.body.get! == some "Either$Elim"
       | none => false


/-! Nested matches -/

private def pNested : Strata.Program :=
#strata
program CoreMatch;

datatype Shape () { Circle(radius : int), Square(side : int) };
datatype Mode  () { Area(), Perimeter() };

function compute(s : Shape, m : Mode) : int
{
  match m {
    arm Area() =>
      match s {
        arm Circle(radius : int) => 3 * radius * radius;
        arm Square(side : int)   => side * side;
      };
    arm Perimeter() =>
      match s {
        arm Circle(radius : int) => 6 * radius;
        arm Square(side : int)   => 4 * side;
      };
  }
};
#end

-- Outer match is on `m`; body is `Mode$Elim`-headed.
#guard match lookupFn pNested "compute" with
       | some f => headOpName f.body.get! == some "Mode$Elim"
       | none => false


/-! Constructor calls in arm bodies -/

private def pBuilds : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function map_inc(xs : List) : List
{
  match xs {
    arm Nil() => Nil();
    arm Cons(hd : int, tl : List) => Cons(hd + 1, map_inc(tl));
  }
};
#end

-- map_inc returns a List, calls Cons in its body, and uses natural
-- recursion: the cata invariant should still hold.
#guard match lookupFn pBuilds "map_inc" with
       | some f => isCataFn "List" f
       | none => false


/-! Statement-level match: ite-shaped procedure body -/

private def pProc : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };

procedure rank(c: Color, out r: int)
spec { ensures r >= 0; ensures r <= 2; }
{
  match c {
    Red()   => { r := 0; }
    Green() => { r := 1; }
    Blue()  => { r := 2; }
  }
};
#end

#guard match lookupProc pProc "rank" with
       | some d => isIteHeadedProc d
       | none => false

-- Spec is preserved: 2 `ensures` clauses.
#guard match lookupProc pProc "rank" with
       | some d => d.spec.postconditions.length == 2
       | none => false


/-! Statement-level match: pattern binders → accessor inits -/

private def pProcWithBinder : Strata.Program :=
#strata
program CoreMatch;

datatype OptInt () { None(), Some(val : int) };

procedure unwrapOr(o: OptInt, dflt: int, out r: int)
{
  match o {
    None()             => { r := dflt; }
    Some(val : int)    => { r := val; }
  }
};
#end

-- Body lowers to ite chain whose Some arm contains
-- `var val : int := OptInt..val(o); r := val;`.  We just confirm
-- the procedure parses and lowers.
#guard match lookupProc pProcWithBinder "unwrapOr" with
       | some d => isIteHeadedProc d
       | none => false


/-! Diagnostics: redundancy / exhaustiveness -/

private def pNonExhaustive : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

function broken(xs : List) : int
{
  match xs {
    arm Nil() => 0;
  }
};
#end

private def pDuplicate : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };

function broken(c : Color) : int
{
  match c {
    arm Red()   => 1;
    arm Red()   => 2;
    arm Green() => 3;
    arm Blue()  => 4;
  }
};
#end

private def pRedundantWild : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };

function broken(c : Color) : int
{
  match c {
    arm Red()   => 1;
    arm Green() => 2;
    arm Blue()  => 3;
    arm _       => 4;
  }
};
#end

private def pUnknownCtor : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };

function broken(c : Color) : int
{
  match c {
    arm Red()    => 1;
    arm Purple() => 2;
    arm Green()  => 3;
    arm Blue()   => 4;
  }
};
#end

#guard parseError? pNonExhaustive
#guard parseError? pDuplicate
#guard parseError? pRedundantWild
#guard parseError? pUnknownCtor


/-! Diagnostics: non-structural recursion -/

private def pBadOtherParam : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function badCall(xs : List, ys : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + badCall(ys, tl);
  }
};
#end

private def pBadSelfApply : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

rec function badSelf(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List) => 1 + badSelf(xs);
  }
};
#end

#guard parseError? pBadOtherParam
#guard parseError? pBadSelfApply


/-! Diagnostics: wrong arm binder count -/

private def pTooFewBinders : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

function bad(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int) => hd;
  }
};
#end

private def pTooManyBinders : Strata.Program :=
#strata
program CoreMatch;

datatype List () { Nil(), Cons(hd : int, tl : List) };

function bad(xs : List) : int
{
  match xs {
    arm Nil() => 0;
    arm Cons(hd : int, tl : List, x : int, y : int) => hd;
  }
};
#end

#guard parseError? pTooFewBinders
#guard parseError? pTooManyBinders


/-! Multiple datatypes, multiple top-level commands -/

private def pMulti : Strata.Program :=
#strata
program CoreMatch;

datatype Color () { Red(), Green(), Blue() };
datatype Mode  () { On(), Off() };

function isRed(c : Color) : bool
{
  match c {
    arm Red()   => true;
    arm Green() => false;
    arm Blue()  => false;
  }
};

function isOn(m : Mode) : bool
{
  match m {
    arm On()  => true;
    arm Off() => false;
  }
};
#end

-- Two datatypes plus two functions; the exact decl count includes
-- auto-generated companions, but it's well-defined and stable.
#guard declCount pMulti == 6

#guard match lookupFn pMulti "isRed" with
       | some f => headOpName f.body.get! == some "Color$Elim"
       | none => false

#guard match lookupFn pMulti "isOn" with
       | some f => headOpName f.body.get! == some "Mode$Elim"
       | none => false


end CoreMatchSourceTest
