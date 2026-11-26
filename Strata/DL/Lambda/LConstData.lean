/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory

/-! # Datatype values and constructor applications

A datatype value (`LConst.dataConst`) stands for the application of its operator to its
arguments. The evaluators of collection operations hold datatype values inside literals, where an
expression cannot occur; these functions move between the two forms, and compare datatype values.

- `LConst.toLExpr` — the expression a constant stands for: a datatype value becomes the
  application of its operator to its arguments.
- `LExpr.toConst?` — the constant an expression stands for: a constant, or a full application of
  a constructor of a factory, at a ground signature, to expressions that stand for constants.
- `Factory.isGroundConstr` — whether a name is a constructor of a factory at a given ground
  signature.
- `LConst.ctorsIn` — whether every datatype value in a constant names such a constructor.
- `LConst.renameData` — a constant with the operators of its datatype values renamed.
- `LConst.eqlIn` — the equality of two constants, deciding datatype values whose operators are
  such constructors by the disjointness and injectivity of constructors.

Their denotations are related in `Strata.DL.Lambda.Denote.LConstDataProps`.
-/

namespace Lambda

public section

variable {T : LExprParams}

/-- The result sort of an `n`-ary function sort: `s` without its first `n` argument sorts. A sort
    with fewer argument sorts is its own result. -/
@[expose] def LSort.dropArrows : Nat → LSort → LSort
  | n + 1, .tcons "arrow" [_, b] => dropArrows n b
  | _, s => s

/-- Whether `n` names a constructor of `F` whose signature is the ground signature `as → s`: its
    input types name the sorts `as` and its output type names `s`. -/
@[expose] def Factory.isGroundConstr (F : Factory T) (n : String) (as : List LSort) (s : LSort) :
    Bool :=
  match F[n]? with
  | some f =>
    f.isConstr && decide (f.output = s.toMonoTy) && decide (f.inputs.values = as.map (·.toMonoTy))
  | none => false

mutual
/-- The expression a constant stands for, with metadata `md`: a datatype value is the application
    of its operator, annotated with its signature, to the expressions of its arguments; any other
    constant is itself. -/
@[expose] def LConst.toLExpr [Inhabited T.IDMeta] (md : T.Metadata) : LConst → LExpr T.mono
  | .dataConst n as s ⟨es⟩ =>
    LConst.toLExprApp md
      (.op md ⟨n, default⟩ (some (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy))))) es
  | .intConst i => .const md (.intConst i)
  | .strConst x => .const md (.strConst x)
  | .rationalConst r => .const md (.rationalConst r)
  | .bitvecConst n b => .const md (.bitvecConst n b)
  | .boolConst b => .const md (.boolConst b)
  | .mapConst k v d es => .const md (.mapConst k v d es)
  | .sequenceConst a es => .const md (.sequenceConst a es)
/-- `f` applied to the expressions of the constants `es`, in order. -/
@[expose] def LConst.toLExprApp [Inhabited T.IDMeta] (md : T.Metadata) (f : LExpr T.mono) :
    List LConst → LExpr T.mono
  | [] => f
  | e :: r => LConst.toLExprApp md (.app md f (LConst.toLExpr md e)) r
end

/-- The datatype value the operator `n`, annotated with `ty`, applied to the constants `cs` stands
    for: when `ty` is the ground signature from the sorts of `cs` to a datatype sort `r`, at which
    `n` is a constructor of `F` (`Factory.isGroundConstr`), and the constants of `cs` are well
    typed. -/
@[expose] def LConst.dataOf? (F : Factory T) (n : String) (ty : LMonoTy) (cs : List LConst) :
    Option LConst :=
  match ty.toSort? with
  | some s =>
    let as := cs.map (·.sort)
    let r := s.dropArrows cs.length
    if decide (s = LSort.mkArrow r as) && F.isGroundConstr n as r && r.isDataSort &&
        LConst.wtArgs as cs then
      some (.dataConst n as r ⟨cs⟩)
    else none
  | none => none

/-- The constant an expression stands for (first component), and, for an application of an
    annotated operator to expressions that stand for constants, the operator's name, its
    annotation and those constants (second component). -/
@[expose] def LExpr.toConstAux (F : Factory T) :
    LExpr T.mono → Option LConst × Option (String × LMonoTy × List LConst)
  | .const _ c => (some c, none)
  | .op _ o (some ty) => (LConst.dataOf? F o.name ty [], some (o.name, ty, []))
  | .app _ f a =>
    let sp := (toConstAux F f).2.bind fun p =>
      (toConstAux F a).1.map fun c => (p.1, p.2.1, p.2.2 ++ [c])
    (sp.bind fun p => LConst.dataOf? F p.1 p.2.1 p.2.2, sp)
  | _ => (none, none)

/-- The constant an expression stands for: a constant is itself, and a full application of a
    constructor of `F`, annotated at a ground signature, to expressions that stand for constants
    is the datatype value of that constructor and those constants (`LConst.dataOf?`). -/
@[expose] def LExpr.toConst? (F : Factory T) (e : LExpr T.mono) : Option LConst :=
  (LExpr.toConstAux F e).1

mutual
/-- Whether every datatype value in a constant names a constructor of `F` at its ground signature
    (`Factory.isGroundConstr`). -/
@[expose] def LConst.ctorsIn (F : Factory T) : LConst → Bool
  | .intConst _ | .strConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _ => true
  | .mapConst _ _ d ⟨es⟩ => d.ctorsIn F && LConst.ctorsInEntries F es
  | .sequenceConst _ ⟨es⟩ => LConst.ctorsInElems F es
  | .dataConst n as s ⟨es⟩ => F.isGroundConstr n as s && LConst.ctorsInElems F es
/-- `LConst.ctorsIn` for every key and value of map entries. -/
@[expose] def LConst.ctorsInEntries (F : Factory T) : List (LConst × LConst) → Bool
  | [] => true
  | (a, b) :: rest => a.ctorsIn F && b.ctorsIn F && LConst.ctorsInEntries F rest
/-- `LConst.ctorsIn` for every element of a list. -/
@[expose] def LConst.ctorsInElems (F : Factory T) : List LConst → Bool
  | [] => true
  | a :: rest => a.ctorsIn F && LConst.ctorsInElems F rest
end

mutual
/-- The equality of two constants of one sort, knowing the constructors of `F`: two datatype
    values whose operators are constructors of `F` at their ground signatures
    (`Factory.isGroundConstr`) are different when their constructors differ, and otherwise
    compare as their arguments (`LConst.eqlInArgs`). Any other two constants compare by
    `LConst.eql`: equal when they are equal, and different when they differ and are both
    `LConst.eqDecidable`. `none` when undecided. -/
@[expose] def LConst.eqlIn (F : Factory T) : LConst → LConst → Option Bool
  | .dataConst n₁ as₁ s₁ ⟨xs⟩, .dataConst n₂ as₂ s₂ ⟨ys⟩ =>
    if n₁ = n₂ ∧ as₁ = as₂ ∧ s₁ = s₂ ∧ xs = ys then some true
    else if F.isGroundConstr n₁ as₁ s₁ && F.isGroundConstr n₂ as₂ s₂ then
      if n₁ = n₂ then LConst.eqlInArgs F xs ys else some false
    else none
  | c₁, c₂ => LConst.eql c₁ c₂
/-- `LConst.eqlIn` of the arguments of two datatype values, position by position: different when
    two arguments are, equal when all are, and `none` otherwise. -/
@[expose] def LConst.eqlInArgs (F : Factory T) : List LConst → List LConst → Option Bool
  | x :: xs, y :: ys =>
    match LConst.eqlIn F x y, LConst.eqlInArgs F xs ys with
    | some false, _ | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | [], [] => some true
  | _, _ => none
end

mutual
/-- Rename the operator of every datatype value in a constant, of sort `srt`
    (`LSort.mkArrow sort argSorts`), from `n` to `f n srt`. -/
@[expose] def LConst.renameData (f : String → LSort → String) : LConst → LConst
  | .intConst i => .intConst i
  | .strConst x => .strConst x
  | .rationalConst r => .rationalConst r
  | .bitvecConst n b => .bitvecConst n b
  | .boolConst b => .boolConst b
  | .mapConst k v d ⟨es⟩ => .mapConst k v (d.renameData f) ⟨LConst.renameDataEntries f es⟩
  | .sequenceConst a ⟨es⟩ => .sequenceConst a ⟨LConst.renameDataElems f es⟩
  | .dataConst n as s ⟨es⟩ =>
    .dataConst (f n (LSort.mkArrow s as)) as s ⟨LConst.renameDataElems f es⟩
/-- `LConst.renameData` on the keys and values of map entries. -/
@[expose] def LConst.renameDataEntries (f : String → LSort → String) :
    List (LConst × LConst) → List (LConst × LConst)
  | [] => []
  | (a, b) :: rest => (a.renameData f, b.renameData f) :: LConst.renameDataEntries f rest
/-- `LConst.renameData` on a list of constants. -/
@[expose] def LConst.renameDataElems (f : String → LSort → String) : List LConst → List LConst
  | [] => []
  | a :: rest => a.renameData f :: LConst.renameDataElems f rest
end

end -- public section

end Lambda
