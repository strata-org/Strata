/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ContextualRewrite.Engine
public import Strata.Languages.Core.NameMangling
public import Strata.DL.Lambda.LExprRenameOps
public import Strata.DL.Lambda.LExprType

/-! # Contextual rewriting: the theories

The rewrite rules of the contextual rewriting engine (`ContextualRewrite.Engine`), as
conditional rules (`CondRule`) grouped in theories. Each theory recognizes its operators in
the program's function table and checks that they have the signatures (and, for maps and
sequences, the axioms) its rules rely on; an operator that fails a check is not recognized,
and no rule applies to it.

## The rewrites

Hypotheses follow "if"; the engine discharges them by rewriting (`CondRule`).

* Boolean:
  * `a ∧ true → a`, `true ∧ a → a`, `a ∧ false → false`;
  * `a ∨ false → a`, `false ∨ a → a`, `a ∨ true → true`;
  * `true ⇒ a → a`, `a ⇒ true → true`, `a ⇒ false → ¬a` (`false ∧ a`, `true ∨ a` and
    `false ⇒ a` become their value in the engine);
  * `¬¬a → a`, `¬true → false`, `¬false → true`;
  * `ite c x x → x` (an `ite` with a literal condition becomes its branch in the engine);
  * `ite c true false → c`, `ite c false true → ¬c`, `ite c x false → c ∧ x`,
    `ite c true x → c ∨ x`, `ite c false x → ¬c ∧ x`, `ite c x true → c ⇒ x`;
  * `a == true → a`, `a == false → ¬a` (either side);
  * `∀x. true → true`, `∃x. false → false`.
* Equality: `a == a → true`; `l₁ == l₂ → false` for different literals `l₁`, `l₂` of the
  same kind.
* Datatypes, for constructors `C ≠ D` of one datatype:
  * `isC(C(…)) → true`, `isC(D(…)) → false`;
  * `sel_i(C(a₁, …, aₙ)) → aᵢ` for the selector of the `i`-th field of `C`;
  * `C(a₁, …, aₙ) == D(b₁, …, bₘ) → false`;
  * `C(a₁, …, aₙ) == C(b₁, …, bₙ) → a₁ == b₁ ∧ … ∧ aₙ == bₙ` (`true` for `n = 0`);
  * `isD(t) → false if isC₁(t) ∨ … ∨ isCₖ(t)`, over the other constructors `Cᵢ`;
  * `isC(t) → true if ¬isD₁(t) ∧ … ∧ ¬isDₖ(t)`, over all other constructors `Dᵢ`; the tester
    of the only constructor of a datatype is `true`;
  * `f(ite g a b) → ite g (f a) (f b)` for a tester or selector `f`, and
    `ite g a b == y → ite g (a == y) (b == y)` (either side).
* Maps, for `select`, `update` and `const` of one family:
  * `select(update(m, k, v), k') → v if k == k'`;
  * `select(update(m, k, v), k') → select(m, k') if ¬(k == k')`;
  * `select(const(v), k) → v`;
  * `select(ite g a b, k) → ite g (select(a, k)) (select(b, k))`.
* Sequences, for `length`, `build` and `empty` of one family:
  * `length(build(s, x)) → length(s) + 1`, `length(empty) → 0`;
  * `length(ite g a b) → ite g (length(a)) (length(b))`.
* Integers: `x + c ≤ x + d → c ≤ d` and the same for the other comparisons, for literals
  `c`, `d` and `x` itself read as `x + 0`;
  `lo ≤ x ∧ x < hi → false if hi ≤ lo` and `lo ≤ x ∧ x ≤ hi → false if ¬(lo ≤ hi)`, for
  literals `lo`, `hi`.
* Evaluation: `f(a₁, …, aₙ) → r` when the evaluator of the function `f` (`LFunc.concreteEval`)
  gives `r` on the arguments (values, or where `f`'s attributes say so, a constructor
  application or a value at one position), `r` type checks (`LExpr.typeCheckWith`) with the
  type of the application, and `r` mentions only variables of the arguments. This covers
  integer arithmetic and comparisons on literals and the length of a sequence literal.
  Function bodies are not unfolded.

The engine reads through a variable's definition at the argument of a tester, selector, map
read (the map) and sequence length, and at a side of an equation whose other side is a
constructor application or a literal (`CondRule.needsHead`).

## Recognizing operators

An operator is a function of the program's function table, by its name. Map and sequence
operators are polymorphic in Core, and monomorphization replaces them with copies at each
type they are used at, named by `NameMangling.copyName` (`$__mono#select#int#int` is
`select` at `Map int int`, under the prefix `$__mono` that monomorphization picks unless a
name of the program starts with it) and marked as copies (`FuncAttr.monoCopyOf`). The
theories read a name as a copy's only for a function so marked (`readName`): a function the
program declares can be named like a copy, and it means what its own declaration says. Two
copies are related only when they belong to one family: neither named as a copy, or both
named as copies with the same prefix and instantiation, so that a `select` copy pairs with
the `update` copy of its own instance. Copies of testers and selectors are read the same way,
and a tester copy's siblings are the copies of the other testers. Each recognized
operator must have the signature its kind expects (for example, `Map k v → k → v` for a
map read), and a map or sequence copy must carry Core's axioms instantiated at its type and
renamed to the copies of its family, since the rules are only as sound as those axioms.
Boolean connectives and integer operations are not polymorphic, so monomorphization does not
copy them: the theories recognize them by their Core names only (`Bool.And`, `Int.Lt`, …).

## The operators the rules build

The rules build terms with `¬`, `∧`, `∨`, `⇒` (the `ite` rules, the hypotheses of the
tester and map rules) and integer addition `+` (`length(build(s, x)) → length(s) + 1`),
using Core's functions `Bool.Not`, `Bool.And`, `Bool.Or`, `Bool.Implies` and `Int.Add`. The
environment checks that the function table has these functions with their Core signatures;
when it does not, the engine is off: it learns no fact and rewrites nothing.

## Soundness

Every rule of these theories, when its hypotheses hold, rewrites a term to one with the same
value, so the environment they build is sound. This holds for a function table that keeps
Core's connectives and integer operations and has the generated datatype functions, in every
model consistent with the table whose datatype testers mean what they say.
-/

namespace Core.ContextualRewrite

open Lambda hiding Env

public section

/-! ## Shared helpers -/

/-- The signature of `f`, as the arrow from its input types to its output type. -/
def sigOf (f : LFunc CoreLParams) : LMonoTy :=
  LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)

/-- Whether `f` is a copy monomorphization made: it is marked as the copy of a function
    (`FuncAttr.monoCopyOf b`), and its name, read as a copy's under the prefix it carries
    (`NameMangling.demangledBaseNameAnyPrefix`), is `b`. -/
def isMonoCopy (f : LFunc CoreLParams) : Bool :=
  Strata.DL.Util.FuncAttr.findMonoCopyOf f.attr ==
    some (NameMangling.demangledBaseNameAnyPrefix f.name.name)

/-- The name the theories read `f` by: for a copy monomorphization made (`isMonoCopy`), the
    name of the function it copies; for any other function, its own name. For example, the
    marked copy `$__mono#select#int#int` is read as `select`, and an unmarked function of that
    name as itself. -/
def readName (f : LFunc CoreLParams) : String :=
  if isMonoCopy f then NameMangling.demangledBaseNameAnyPrefix f.name.name else f.name.name

/-- The prefix and the instantiation part of the name `n` of a copy, or `none` when `n` does
    not have a copy's shape (`NameMangling.copyPrefixOf?`). -/
def copyFamily? (n : String) : Option (String × String) :=
  (NameMangling.copyPrefixOf? n).bind fun pfx =>
    (NameMangling.demangleFuncName pfx n).map fun (_, tys) => (pfx, tys)

/-- Whether two operators belong to the same family: neither has a copy's name, or both have
    copies' names with the same prefix and the same instantiation. -/
def sameFamily (a b : String) : Bool := copyFamily? a == copyFamily? b

/-- The Core operation the function `f` is, by the name it is read by (`readName`). -/
def coreOpOf (f : LFunc CoreLParams) : CoreOp := CoreOp.ofString (readName f)

/-- Whether the operator `e` is a function of `F` annotated with an instance of its
    signature. -/
def opConsistent (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Bool :=
  match e with
  | .op _ name (some ty) =>
    match F[name.name]? with
    | some fn =>
      match LFunc.opTypeSubst fn e with
      | some S => ty == (sigOf fn).subst S
      | none => false
    | none => false
  | _ => false

/-- The integer literal `e` denotes. -/
def intLit? : Expression.Expr → Option Int
  | .const _ (.intConst i) => some i
  | _ => none

/-- `¬ a`. -/
def mkNot (a : Expression.Expr) : Expression.Expr := .app valueLoc boolNotOp a

/-- `a ∧ b`. -/
def mkAnd (a b : Expression.Expr) : Expression.Expr :=
  .app valueLoc (.app valueLoc boolAndOp a) b

/-- `a ∨ b`. -/
def mkOr (a b : Expression.Expr) : Expression.Expr :=
  .app valueLoc (.app valueLoc boolOrOp a) b

/-- `a ⇒ b`. -/
def mkImplies (a b : Expression.Expr) : Expression.Expr :=
  .app valueLoc (.app valueLoc boolImpliesOp a) b

/-- Whether a head is an operator whose name `p` accepts. -/
@[inline] def opHead (p : String → Bool) : Head → Bool
  | .op n => p n
  | _ => false

/-! ## Boolean -/

/-- The Boolean connectives of a function table. -/
structure BoolEnv where
  /-- The connective each function denotes, for the functions with the name of a Core
      connective and its signature (`bool → bool` for `¬`, `bool → bool → bool` for the
      others). -/
  connectives : Std.HashMap String BoolOpKind := {}

/-- The connectives of `F`. -/
def BoolEnv.ofFactory (F : Lambda.Factory CoreLParams) : BoolEnv :=
  { connectives := F.toArray.foldl (init := {}) fun m f =>
      match CoreOp.ofString f.name.name with
      | .bool k =>
        let fits : Bool := if k == .Not then sigOf f == .arrow .bool .bool
          else sigOf f == .arrow .bool (.arrow .bool .bool)
        if fits then m.insert f.name.name k else m
      | _ => m }

namespace BoolEnv

/-- Whether `h` is the connective `k`. -/
def isConn (b : BoolEnv) (k : BoolOpKind) (h : Head) : Bool :=
  opHead (fun n => b.connectives.get? n == some k) h

/-- `e` as a connective applied to its operands. -/
@[inline] def conn? (b : BoolEnv) (e : Expression.Expr) : Option Conn :=
  Conn.of? b.connectives e

end BoolEnv

/-- `a ∧ true → a`, `true ∧ a → a`, `a ∧ false → false`. Example: `p ∧ true → p`. A
    conjunction whose first operand rewrites to `false` becomes `false` before rules are
    tried. -/
def andRule : CondRule BoolEnv where
  name := "and"
  heads b := b.isConn .And
  apply b e := do
    let some (.bin .and x y) := b.conn? e | none
    match x.denoteBool, y.denoteBool with
    | _, some false => some (boolLit false, [])
    | some true, _ => some (y, [])
    | _, some true => some (x, [])
    | _, _ => none

/-- `a ∨ false → a`, `false ∨ a → a`, `a ∨ true → true`. Example: `false ∨ p → p`. A
    disjunction whose first operand rewrites to `true` becomes `true` before rules are
    tried. -/
def orRule : CondRule BoolEnv where
  name := "or"
  heads b := b.isConn .Or
  apply b e := do
    let some (.bin .or x y) := b.conn? e | none
    match x.denoteBool, y.denoteBool with
    | _, some true => some (boolLit true, [])
    | some false, _ => some (y, [])
    | _, some false => some (x, [])
    | _, _ => none

/-- `true ⇒ a → a`, `a ⇒ true → true`, `a ⇒ false → ¬a`. Example: `p ⇒ false → ¬p`. An
    implication whose antecedent rewrites to `false` becomes `true` before rules are
    tried. -/
def impliesRule : CondRule BoolEnv where
  name := "implies"
  heads b := b.isConn .Implies
  apply b e := do
    let some (.bin .implies x y) := b.conn? e | none
    match x.denoteBool, y.denoteBool with
    | _, some true => some (boolLit true, [])
    | some true, _ => some (y, [])
    | _, some false => some (mkNot x, [])
    | _, _ => none

/-- `¬¬a → a`, `¬true → false`, `¬false → true`. Example: `¬¬p → p`. -/
def notRule : CondRule BoolEnv where
  name := "not"
  heads b := b.isConn .Not
  apply b e := do
    let some (.not a) := b.conn? e | none
    match a.denoteBool, b.conn? a with
    | some c, _ => some (boolLit (!c), [])
    | none, some (.not a') => some (a', [])
    | none, _ => none

/-- `ite c x x → x`. Example: `ite p q q → q`. An `ite` whose condition rewrites to a literal
    is replaced by its branch before rules are tried. -/
def iteRule : CondRule BoolEnv where
  name := "ite"
  heads _ h := h matches .ite
  apply _ e := match e with
    | .ite _ _ a b => if a.beqIgnoringMetadata b then some (a, []) else none
    | _ => none

/-- A Boolean `ite` with a literal branch as a connective: `ite c true false → c`,
    `ite c false true → ¬c`, `ite c x false → c ∧ x`, `ite c true x → c ∨ x`,
    `ite c false x → ¬c ∧ x`, `ite c x true → c ⇒ x`. Example: `ite p q false → p ∧ q`. -/
def iteBoolRule : CondRule BoolEnv where
  name := "ite-bool"
  heads _ h := h matches .ite
  apply _ e := match e with
    | .ite _ c (.const _ (.boolConst true)) (.const _ (.boolConst false)) => some (c, [])
    | .ite _ c (.const _ (.boolConst false)) (.const _ (.boolConst true)) => some (mkNot c, [])
    | .ite _ c x (.const _ (.boolConst false)) => some (mkAnd c x, [])
    | .ite _ c (.const _ (.boolConst true)) x => some (mkOr c x, [])
    | .ite _ c (.const _ (.boolConst false)) x => some (mkAnd (mkNot c) x, [])
    | .ite _ c x (.const _ (.boolConst true)) => some (mkImplies c x, [])
    | _ => none

/-- `a == true → a`, `a == false → ¬a`, on either side. Example: `p == false → ¬p`. -/
def eqBoolRule : CondRule BoolEnv where
  name := "eq-bool"
  heads _ h := h matches .eq
  apply _ e := match e with
    | .eq _ a (.const _ (.boolConst true)) => some (a, [])
    | .eq _ (.const _ (.boolConst true)) b => some (b, [])
    | .eq _ a (.const _ (.boolConst false)) => some (mkNot a, [])
    | .eq _ (.const _ (.boolConst false)) b => some (mkNot b, [])
    | _ => none

/-- `∀x. true → true`, `∃x. false → false`. Example: `∀k. true → true`. -/
def quantRule : CondRule BoolEnv where
  name := "quant"
  heads _ h := h matches .quant
  apply _ e := match e with
    | .quant _ .all _ _ _ (.const _ (.boolConst true)) => some (boolLit true, [])
    | .quant _ .exist _ _ _ (.const _ (.boolConst false)) => some (boolLit false, [])
    | _ => none

/-- The rules of the Boolean theory, in the order they are tried. -/
def booleanRules : List (CondRule BoolEnv) :=
  [andRule, orRule, impliesRule, notRule, iteRule, iteBoolRule, eqBoolRule, quantRule]

/-! ## Equality -/

/-- Whether two constants are equal, when comparing them settles it: equal constants are
    equal, and different integer, string, real, Boolean, or same-width bitvector literals are
    different. -/
def constEq? (a b : LConst) : Option Bool :=
  if a == b then some true
  else match a, b with
    | .intConst _, .intConst _ | .strConst _, .strConst _
    | .rationalConst _, .rationalConst _ | .boolConst _, .boolConst _ => some false
    | .bitvecConst n _, .bitvecConst m _ => if n == m then some false else none
    | _, _ => none

/-- `a == a → true`. Example: `f(x) == f(x) → true`. -/
def eqSelfRule : CondRule Unit where
  name := "eq-self"
  heads _ h := h matches .eq
  apply _ e := match e with
    | .eq _ a b => if a.beqIgnoringMetadata b then some (boolLit true, []) else none
    | _ => none

/-- Different literals of the same kind are not equal. Example: `1 == 2 → false`. The engine
    reads through a variable's definition on one side when the other is a literal. -/
def eqLitRule : CondRule Unit where
  name := "eq-literals"
  heads _ h := h matches .eq
  needsHead _ e := match e with
    | .eq _ a b => (if isConst b then [0] else []) ++ (if isConst a then [1] else [])
    | _ => []
  apply _ e := match e with
    | .eq _ (.const _ x) (.const _ y) => (constEq? x y).map (boolLit ·, [])
    | _ => none

/-- The rules of the equality theory. -/
def equalityRules : List (CondRule Unit) := [eqSelfRule, eqLitRule]

/-! ## Datatypes -/

/-- What the rules need to know about the constructor a tester tests for. -/
structure CtorInfo where
  /-- The constructor's name. -/
  ctor : String
  /-- The testers of the other constructors of its datatype that are functions of the table,
      named like the tester (`siblingName`) and with the tester's signature. -/
  siblings : List String
  /-- Whether every other constructor's tester is among `siblings`. -/
  complete : Bool
  deriving Inhabited

/-- The datatype operators of a function table. -/
structure DatatypeEnv where
  /-- The tester table: for each tester function (`T..isC`, of type `T → bool`), the
      constructor it tests for and the testers of the other constructors. -/
  testers : Std.HashMap String CtorInfo := {}
  /-- The selector table: for each selector function (`T..f`, of type `T → r`), the
      constructor whose field it reads and the field's index. -/
  selectors : Std.HashMap String (String × Nat) := {}
  /-- The constructor functions of the program's datatypes, with their arities. -/
  ctors : Std.HashMap String Nat := {}

/-- The testers and selectors the datatypes `dts` define, by name: for a tester, its
    constructor and the testers of the other constructors; for a selector, its constructor
    and field index. A name two datatypes give is left out. -/
def datatypeTables (dts : List (LDatatype Unit)) :
    Std.HashMap String (String × List String) × Std.HashMap String (String × Nat) := Id.run do
  let mut testers : Std.HashMap String (Option (String × List String)) := {}
  let mut selectors : Std.HashMap String (Option (String × Nat)) := {}
  for d in dts do
    for c in d.constrs do
      let siblings := (d.constrs.filter (·.name.name != c.name.name)).map (·.testerName)
      testers := testers.insert c.testerName
        (if testers.contains c.testerName then none else some (c.name.name, siblings))
      let mut idx := 0
      for (field, _) in c.args do
        let sel := destructorFuncName d field
        selectors := selectors.insert sel
          (if selectors.contains sel then none else some (c.name.name, idx))
        idx := idx + 1
  let keep {α : Type} (m : Std.HashMap String (Option α)) : Std.HashMap String α :=
    m.fold (init := {}) fun acc k v => match v with | some v => acc.insert k v | none => acc
  return (keep testers, keep selectors)

/-- The name of the tester `sib` as a sibling of the tester `f : T τs → bool`: for a copy
    monomorphization made, the name of the copy of `sib` at `τs` under `f`'s prefix
    (`NameMangling.copyName`); otherwise `sib` itself. -/
def siblingName (f : LFunc CoreLParams) (sib : String) : String :=
  if isMonoCopy f then
    match NameMangling.copyPrefixOf? f.name.name, f.inputs with
    | some pfx, [(_, .tcons _ tys)] => NameMangling.copyName pfx sib tys
    | _, _ => sib
  else sib

/-- The datatype operators of `F` for the datatypes `dts`. A tester or selector is recognized
    by the name it is read by (`readName`) and must have the type `T → bool` or `T → r`; a
    constructor by its own name, as a constructor function of `F` with the arity of its
    declaration. A tester's siblings are the testers of the other constructors with its
    signature (`siblingName`), so that a sibling applied as the tester is consistent with `F`.
    For example, with `datatype T { A(a : int), B() }`, `T..isA : T → bool` is the tester of
    `A` with sibling `T..isB`, `T..a : T → int` is the selector of field `0` of `A`, and `A`
    and `B` are constructors of arities `1` and `0`; a function `$__mono#T..isA#int` is the
    tester of `A` only when it is marked as the copy of `T..isA`. -/
def DatatypeEnv.ofFactory (F : Lambda.Factory CoreLParams) (dts : List (LDatatype Unit)) :
    DatatypeEnv :=
  let (testerTable, selectorTable) := datatypeTables dts
  let ctorArity : Std.HashMap String Nat := dts.foldl (init := {}) fun m d =>
    d.constrs.foldl (init := m) fun m c => m.insert c.name.name c.args.length
  let isTesterTy : LMonoTy → Bool
    | .tcons "arrow" [_, .tcons "bool" []] => true
    | _ => false
  let isSelectorTy : LMonoTy → Bool
    | .tcons "arrow" [_, _] => true
    | _ => false
  let testerSigs : Std.HashMap String LMonoTy := F.toArray.foldl (init := {}) fun s f =>
    if testerTable.contains (readName f) && isTesterTy (sigOf f)
    then s.insert f.name.name (sigOf f) else s
  F.toArray.foldl (init := {}) fun env f =>
    let name := f.name.name
    let base := readName f
    let env :=
      match testerTable.get? base with
      | some (ctor, sibs) =>
        if !testerSigs.contains name then env else
        let named := sibs.map (siblingName f)
        let present := named.filter fun s => testerSigs.get? s == some (sigOf f)
        let info : CtorInfo :=
          { ctor := ctor, siblings := present, complete := present.length == named.length }
        { env with testers := env.testers.insert name info }
      | none => env
    let env :=
      match selectorTable.get? base with
      | some info =>
        if isSelectorTy (sigOf f) then { env with selectors := env.selectors.insert name info }
        else env
      | none => env
    match ctorArity.get? name with
    | some n =>
      if f.isConstr && f.inputs.length == n then { env with ctors := env.ctors.insert name n }
      else env
    | none => env

namespace DatatypeEnv

/-- `e` as a full application of a constructor: the constructor's name and its arguments.
    For example, `A(1)` is `("A", [1])` and `C` is `("C", [])`. -/
def ctorApp? (dt : DatatypeEnv) (e : Expression.Expr) :
    Option (String × List Expression.Expr) :=
  match e with
  | .op _ o _ => if dt.ctors.get? o.name == some 0 then some (o.name, []) else none
  | .app .. =>
    match spine? e [] with
    | some (.op _ o _, args) =>
      if dt.ctors.get? o.name == some args.length then some (o.name, args.map (·.2)) else none
    | _ => none
  | _ => none

/-- Whether `h` is a tester. -/
def isTester (dt : DatatypeEnv) : Head → Bool := opHead dt.testers.contains

/-- Whether `h` is a tester or a selector. -/
def isTesterOrSelector (dt : DatatypeEnv) : Head → Bool :=
  opHead fun n => dt.testers.contains n || dt.selectors.contains n

end DatatypeEnv

/-- `isC(C(…)) → true`, `isC(D(…)) → false`. Example: `isA(A(1)) → true`. -/
def testerCtorRule : CondRule DatatypeEnv where
  name := "tester-ctor"
  heads dt := dt.isTester
  needsHead _ _ := [0]
  apply dt e := match e with
    | .app _ (.op _ o _) a => do
      let info ← dt.testers.get? o.name
      let (c, _) ← dt.ctorApp? a
      some (boolLit (c == info.ctor), [])
    | _ => none

/-- `sel_i(C(a₁, …, aₙ)) → aᵢ` for the selector of the `i`-th field of `C`. Example:
    `T..a(A(y)) → y`. The evaluation rule does the same only when the term type checks on its
    own, which fails when an argument mentions a bound variable. -/
def selectorCtorRule : CondRule DatatypeEnv where
  name := "selector-ctor"
  heads dt := opHead dt.selectors.contains
  needsHead _ _ := [0]
  apply dt e := match e with
    | .app _ (.op _ o _) a => do
      let (ctor, idx) ← dt.selectors.get? o.name
      let (c, args) ← dt.ctorApp? a
      if c == ctor then (args[idx]?).map (·, []) else none
    | _ => none

/-- The tester `s` applied to `a`, at the location and with the annotation of the tester
    application `isC(a)` it is derived from. -/
def siblingProbe (m mo : ExprSourceLoc) (ty : Option LMonoTy) (s : String)
    (a : Expression.Expr) : Expression.Expr :=
  .app m (.op mo ⟨s, ()⟩ ty) a

/-- `isD(t) → false if isC₁(t) ∨ … ∨ isCₖ(t)`, over the testers of the other constructors.
    Example: with the fact `isA(x)`, `isB(x) → false`. The hypothesis holds only by the facts
    directly. -/
def testerOtherRule : CondRule DatatypeEnv where
  name := "tester-other"
  heads dt := dt.isTester
  needsHead _ _ := [0]
  hypDepth := some 0
  apply dt e := match e with
    | .app m (.op mo o ty) a => do
      let info ← dt.testers.get? o.name
      match info.siblings with
      | [] => none
      | s :: ss =>
        let probe := siblingProbe m mo ty
        some (boolLit false, [ss.foldl (fun acc s' => mkOr acc (probe s' a)) (probe s a)])
    | _ => none

/-- `isC(t) → true if ¬isD₁(t) ∧ … ∧ ¬isDₖ(t)`, over the testers of all other constructors;
    the tester of the only constructor of a datatype is `true`. Example: with the facts
    `¬isA(x)` and `¬isB(x)`, `isC(x) → true`. The hypotheses hold only by the facts
    directly. -/
def testerExhaustRule : CondRule DatatypeEnv where
  name := "tester-exhaust"
  heads dt := dt.isTester
  needsHead _ _ := [0]
  hypDepth := some 0
  apply dt e := match e with
    | .app m (.op mo o ty) a => do
      let info ← dt.testers.get? o.name
      if !info.complete then none
      else some (boolLit true, info.siblings.map fun s => mkNot (siblingProbe m mo ty s a))
    | _ => none

/-- `C(a₁, …, aₙ) == D(b₁, …, bₘ) → false` for different constructors. Example:
    `A(y) == B(z) → false`. The engine reads through a variable's definition on one side when
    the other is a constructor application. -/
def eqCtorDiffRule : CondRule DatatypeEnv where
  name := "eq-ctor-different"
  heads _ h := h matches .eq
  needsHead dt e := match e with
    | .eq _ a b => (if (dt.ctorApp? b).isSome then [0] else []) ++
        (if (dt.ctorApp? a).isSome then [1] else [])
    | _ => []
  apply dt e := match e with
    | .eq _ a b => do
      let (ca, _) ← dt.ctorApp? a
      let (cb, _) ← dt.ctorApp? b
      if ca != cb then some (boolLit false, []) else none
    | _ => none

/-- `C(a₁, …, aₙ) == C(b₁, …, bₙ) → a₁ == b₁ ∧ … ∧ aₙ == bₙ`, and `true` for `n = 0`.
    Example: `A(y) == A(z) → y == z`. -/
def eqCtorSameRule : CondRule DatatypeEnv where
  name := "eq-ctor-same"
  heads _ h := h matches .eq
  apply dt e := match e with
    | .eq m a b => do
      let (ca, as) ← dt.ctorApp? a
      let (cb, bs) ← dt.ctorApp? b
      if ca != cb || as.length != bs.length then none else
      match (as.zip bs).map fun (x, y) => (LExpr.eq m x y : Expression.Expr) with
      | [] => some (boolLit true, [])
      | q :: qs => some (qs.foldl mkAnd q, [])
    | _ => none

/-- `f(ite g a b) → ite g (f a) (f b)` for a tester or selector `f`. Example:
    `isA(ite p A(1) x) → ite p isA(A(1)) isA(x)`. -/
def pushIteDatatypeRule : CondRule DatatypeEnv where
  name := "push-ite-tester-selector"
  heads dt := dt.isTesterOrSelector
  needsHead _ _ := [0]
  apply _ e := match e with
    | .app m fn@(.op ..) (.ite mi g a b) => some (.ite mi g (.app m fn a) (.app m fn b), [])
    | _ => none

/-- `ite g a b == y → ite g (a == y) (b == y)`, on either side. Example:
    `ite p y z == y → ite p (y == y) (z == y)`. -/
def pushIteEqRule : CondRule DatatypeEnv where
  name := "push-ite-eq"
  heads _ h := h matches .eq
  apply _ e := match e with
    | .eq m (.ite mi g a b) y => some (.ite mi g (.eq m a y) (.eq m b y), [])
    | .eq m x (.ite mi g a b) => some (.ite mi g (.eq m x a) (.eq m x b), [])
    | _ => none

/-- The rules of the datatype theory, in the order they are tried. -/
def datatypeRules : List (CondRule DatatypeEnv) :=
  [testerCtorRule, selectorCtorRule, testerOtherRule, testerExhaustRule, eqCtorDiffRule,
    eqCtorSameRule, pushIteDatatypeRule, pushIteEqRule]

/-! ## Maps -/

/-- The map operators the theory recognizes. -/
inductive MapOp where
  | select | update | const
  deriving Inhabited, BEq

/-- The map operators of a function table. -/
structure MapEnv where
  /-- Each map operator by name: a function named after Core's `select`, `update` or
      `mapConst` (by `readName`), with its signature, and, for `update` and `const`,
      the axioms the rules read. -/
  ops : Std.HashMap String MapOp := {}

/-- The operator names the pairs `l` map, and every other name unchanged. -/
@[expose] def renameBy (l : List (String × String)) (n : String) : String := (l.lookup n).getD n

/-- The axiom `ax` with its type variables substituted by `S` and its operators renamed by
    `l`. -/
@[expose] def instAx (S : Subst) (l : List (String × String)) (ax : Expression.Expr) :
    Expression.Expr :=
  (ax.applyTypeSubst S).renameOps (fun o _ => ⟨renameBy l o.name, ()⟩)

/-- The substitution reading the type variables `l` names as the types it pairs them with. -/
@[expose] def tySubstOf (l : List (String × LMonoTy)) : Subst :=
  [l.foldl (fun m (x, t) => m.insert x t) Strata.Util.HMap.empty]

/-- Whether `f` has the axiom `ax` of Core's function, with its type variables read by `S`
    and Core's operator names read by `l`. -/
def hasAxiom (f : LFunc CoreLParams) (S : Subst) (l : List (String × String))
    (ax : Expression.Expr) : Bool :=
  haveI : DecidableEq CoreLParams.mono.base.Metadata :=
    show DecidableEq ExprSourceLoc from inferInstance
  haveI : DecidableEq (LExpr CoreLParams.mono) := inferInstance
  f.axioms.any fun a => Decidable.decide (a = instAx S l ax)

/-- The map operator `f` is by the name it is read by (`readName`) and its signature: a read
    `Map k v → k → v`, an update `Map k v → k → v → Map k v`, or a constant map
    `v → Map k v`. For example, the copy `$__mono#select#int#int : Map int int → int → int`
    is a read, and a function named
    `select` with another signature is none. -/
def mapOpOf? (f : LFunc CoreLParams) : Option MapOp :=
  match coreOpOf f, sigOf f with
  | .map .Select, .tcons "arrow" [.tcons "Map" [k, v], .tcons "arrow" [k', v']] =>
    if k == k' && v == v' then some .select else none
  | .map .Update, .tcons "arrow" [.tcons "Map" [k, v],
      .tcons "arrow" [k', .tcons "arrow" [v', .tcons "Map" [k'', v'']]]] =>
    if k == k' && k == k'' && v == v' && v == v'' then some .update else none
  | .map .Const, .tcons "arrow" [v, .tcons "Map" [_, v']] =>
    if v == v' then some .const else none
  | _, _ => none

/-- The map operators of `F`. An update or a constant map is recognized only when it carries,
    for each read of its family, the instances of Core's axioms that relate the two: the
    axioms of Core's function of its kind, with their type variables read at its signature and
    Core's names read as the two operators'. -/
def MapEnv.ofFactory (F : Lambda.Factory CoreLParams) : MapEnv :=
  let shaped := F.toArray.toList.filterMap fun f => (mapOpOf? f).map (f, ·)
  let selects (f : LFunc CoreLParams) : List String := shaped.filterMap fun (g, k) =>
    if k == .select && sameFamily g.name.name f.name.name then some g.name.name else none
  let lawful (f : LFunc CoreLParams) (k : MapOp) : Bool :=
    match k, f.inputs.map Prod.snd, f.output with
    | .select, _, _ => true
    | .update, [.tcons "Map" [kt, vt], _, _], _ =>
      let S := tySubstOf [("k", kt), ("v", vt)]
      (selects f).all fun so =>
        hasAxiom f S [("select", so), ("update", f.name.name)] (mapUpdateFunc.func.axioms[0]!) &&
        hasAxiom f S [("select", so), ("update", f.name.name)] (mapUpdateFunc.func.axioms[1]!)
    | .const, [_], .tcons "Map" [kt, vt] =>
      let S := tySubstOf [("k", kt), ("v", vt)]
      (selects f).all fun so =>
        hasAxiom f S [("select", so), ("mapConst", f.name.name)] (mapConstFunc.func.axioms[0]!)
    | _, _, _ => false
  { ops := shaped.foldl (init := {}) fun m (f, k) =>
      if lawful f k then m.insert f.name.name k else m }

/-- The parts of a map read of an update, `select(update(m, k, v), k')`: the read with `m` in
    place of the update, `k`, `v` and `k'`, for operators of one family. -/
def MapEnv.selectUpdate? (me : MapEnv) : Expression.Expr →
    Option (Expression.Expr × Expression.Expr × Expression.Expr × Expression.Expr)
  | .app m1 (.app m2 sel@(.op _ so _) (.app _ (.app _ (.app _ (.op _ uo _) mp) k) v)) k' =>
    if me.ops.get? so.name == some .select && me.ops.get? uo.name == some .update &&
        sameFamily so.name uo.name then some (.app m1 (.app m2 sel mp) k', k, v, k')
    else none
  | _ => none

/-- Whether `h` is a map read. -/
def MapEnv.isSelect (me : MapEnv) : Head → Bool := opHead fun n => me.ops.get? n == some .select

/-- `select(update(m, k, v), k') → v if k == k'`. Example: `select(update(m, i, v), i) → v`. -/
def selectUpdateSameRule : CondRule MapEnv where
  name := "select-update-same"
  heads me := me.isSelect
  needsHead _ _ := [0]
  apply me e := do
    let (_, k, v, k') ← me.selectUpdate? e
    some (v, [.eq valueLoc k k'])

/-- `select(update(m, k, v), k') → select(m, k') if ¬(k == k')`. Example: with the fact
    `¬(i == j)`, `select(update(m, i, v), j) → select(m, j)`. -/
def selectUpdateOtherRule : CondRule MapEnv where
  name := "select-update-other"
  heads me := me.isSelect
  needsHead _ _ := [0]
  apply me e := do
    let (below, k, _, k') ← me.selectUpdate? e
    some (below, [mkNot (.eq valueLoc k k')])

/-- `select(const(v), k) → v`. Example: `select(const(0), i) → 0`. -/
def selectConstRule : CondRule MapEnv where
  name := "select-const"
  heads me := me.isSelect
  needsHead _ _ := [0]
  apply me e := match e with
    | .app _ (.app _ (.op _ so _) (.app _ (.op _ co _) v)) _ =>
      if me.ops.get? so.name == some .select && me.ops.get? co.name == some .const &&
          sameFamily so.name co.name then some (v, []) else none
    | _ => none

/-- `select(ite g a b, k) → ite g (select(a, k)) (select(b, k))`. Example:
    `select(ite p m n, i) → ite p (select(m, i)) (select(n, i))`. -/
def pushIteSelectRule : CondRule MapEnv where
  name := "push-ite-select"
  heads me := me.isSelect
  needsHead _ _ := [0]
  apply _ e := match e with
    | .app m1 (.app m2 fn@(.op ..) (.ite mi g a b)) k =>
      some (.ite mi g (.app m1 (.app m2 fn a) k) (.app m1 (.app m2 fn b) k), [])
    | _ => none

/-- The rules of the map theory, in the order they are tried. -/
def mapRules : List (CondRule MapEnv) :=
  [selectConstRule, selectUpdateSameRule, selectUpdateOtherRule, pushIteSelectRule]

/-! ## Sequences -/

/-- The sequence operators the theory recognizes. -/
inductive SeqOp where
  | length | build | empty
  deriving Inhabited, BEq

/-- The sequence operators of a function table. -/
structure SeqEnv where
  /-- Each sequence operator by name: a function named after Core's `Sequence.length`,
      `Sequence.build` or `Sequence.empty` (by `readName`), with its signature, and,
      for `build` and `empty`, the axioms the rules read. -/
  ops : Std.HashMap String SeqOp := {}

/-- The sequence operator `f` is by the name it is read by (`readName`) and its signature: a
    length `Sequence a → int`, a build `Sequence a → a → Sequence a`, or an empty sequence
    `Sequence a`. For example, the copy `$__mono#Sequence.length#int : Sequence int → int` is
    a length. -/
def seqOpOf? (f : LFunc CoreLParams) : Option SeqOp :=
  match coreOpOf f, sigOf f with
  | .seq .Length, .tcons "arrow" [.tcons "Sequence" [_], .tcons "int" []] => some .length
  | .seq .Build, .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [a', .tcons "Sequence" [a'']]] =>
    if a == a' && a == a'' then some .build else none
  | .seq .Empty, .tcons "Sequence" [_] => some .empty
  | _, _ => none

/-- The sequence operators of `F`. A build or an empty sequence is recognized only when it
    carries, for each length of its family, the instance of Core's axiom that relates the
    two. -/
def SeqEnv.ofFactory (F : Lambda.Factory CoreLParams) : SeqEnv :=
  let shaped := F.toArray.toList.filterMap fun f => (seqOpOf? f).map (f, ·)
  let lengths (f : LFunc CoreLParams) : List String := shaped.filterMap fun (g, k) =>
    if k == .length && sameFamily g.name.name f.name.name then some g.name.name else none
  let lawful (f : LFunc CoreLParams) (k : SeqOp) : Bool :=
    match k, f.inputs.map Prod.snd, f.output with
    | .length, _, _ => true
    | .build, [.tcons "Sequence" [a], _], _ =>
      let S := tySubstOf [("a", a)]
      (lengths f).all fun lo =>
        hasAxiom f S [("Sequence.length", lo), ("Sequence.build", f.name.name)]
          (seqBuildFunc.func.axioms[0]!)
    | .empty, [], .tcons "Sequence" [a] =>
      let S := tySubstOf [("a", a)]
      (lengths f).all fun lo =>
        hasAxiom f S [("Sequence.length", lo), ("Sequence.empty", f.name.name)]
          (seqEmptyFunc.func.axioms[0]!)
    | _, _, _ => false
  { ops := shaped.foldl (init := {}) fun m (f, k) =>
      if lawful f k then m.insert f.name.name k else m }

/-- Whether `h` is a sequence length. -/
def SeqEnv.isLength (se : SeqEnv) : Head → Bool := opHead fun n => se.ops.get? n == some .length

/-- `length(build(s, x)) → length(s) + 1`. Example: `length(build(s, 5)) → length(s) + 1`. -/
def lengthBuildRule : CondRule SeqEnv where
  name := "length-build"
  heads se := se.isLength
  needsHead _ _ := [0]
  apply se e := match e with
    | .app m len@(.op _ lo _) (.app _ (.app _ (.op _ bo _) s) _) =>
      if se.ops.get? lo.name == some .length && se.ops.get? bo.name == some .build &&
          sameFamily lo.name bo.name then
        some (.app m (.app m intAddOp (.app m len s)) (.intConst m 1), [])
      else none
    | _ => none

/-- `length(empty) → 0`. Example: `length(Sequence.empty) → 0`. -/
def lengthEmptyRule : CondRule SeqEnv where
  name := "length-empty"
  heads se := se.isLength
  needsHead _ _ := [0]
  apply se e := match e with
    | .app m (.op _ lo _) (.op _ eo _) =>
      if se.ops.get? lo.name == some .length && se.ops.get? eo.name == some .empty &&
          sameFamily lo.name eo.name then some (.intConst m 0, []) else none
    | _ => none

/-- `length(ite g a b) → ite g (length(a)) (length(b))`. Example:
    `length(ite p s t) → ite p (length(s)) (length(t))`. -/
def pushIteLengthRule : CondRule SeqEnv where
  name := "push-ite-length"
  heads se := se.isLength
  needsHead _ _ := [0]
  apply _ e := match e with
    | .app m fn@(.op ..) (.ite mi g a b) => some (.ite mi g (.app m fn a) (.app m fn b), [])
    | _ => none

/-- The rules of the sequence theory, in the order they are tried. -/
def sequenceRules : List (CondRule SeqEnv) :=
  [lengthBuildRule, lengthEmptyRule, pushIteLengthRule]

/-! ## Integers -/

/-- The integer operators of a function table. -/
structure IntEnv where
  /-- Each integer operator by name: a function named `Int.Add`, `Int.Sub`, `Int.Lt`,
      `Int.Le`, `Int.Gt` or `Int.Ge`, with Core's signature for it. -/
  ops : Std.HashMap String NumericOpKind := {}
  /-- The Boolean theory's connectives, for `∧`. -/
  bool : BoolEnv := {}

/-- The integer operators of `F`, with the Boolean theory's `b`. -/
def IntEnv.ofFactory (F : Lambda.Factory CoreLParams) (b : BoolEnv) : IntEnv :=
  { bool := b
    ops := F.toArray.foldl (init := {}) fun m f =>
      match CoreOp.ofString f.name.name with
      | .numeric ⟨.int, k⟩ =>
        let fits : Bool := match k with
          | .Add | .Sub => sigOf f == .arrow .int (.arrow .int .int)
          | .Lt | .Le | .Gt | .Ge => sigOf f == .arrow .int (.arrow .int .bool)
          | _ => false
        if fits then m.insert f.name.name k else m
      | _ => m }

/-- Whether `k` is a comparison. -/
def isComparison (k : NumericOpKind) : Bool := k == .Lt || k == .Le || k == .Gt || k == .Ge

/-- `e` as a base term plus an integer literal: `x + c`, `c + x`, `x - c`, or `x` itself
    with `0`. -/
def IntEnv.offsetOf (ie : IntEnv) (e : Expression.Expr) : Expression.Expr × Int :=
  match e with
  | .app _ (.app _ (.op _ o _) a) b =>
    match ie.ops.get? o.name, intLit? a, intLit? b with
    | some .Add, _, some y => (a, y)
    | some .Add, some x, _ => (b, x)
    | some .Sub, _, some y => (a, -y)
    | _, _, _ => (e, 0)
  | _ => (e, 0)

/-- `x + c ≤ x + d → c ≤ d` for literals `c`, `d`, and the same for the other comparisons;
    `x` alone reads as `x + 0`. Example: `y < y + 1 → 0 < 1`. -/
def offsetCmpRule : CondRule IntEnv where
  name := "int-offsets"
  heads ie := opHead fun n => (ie.ops.get? n).any isComparison
  apply ie e := match e with
    | .app m1 (.app m2 cmp@(.op _ o _) a) b => do
      let k ← ie.ops.get? o.name
      if !isComparison k then none else
      let (ba, ca) := ie.offsetOf a
      let (bb, cb) := ie.offsetOf b
      if isConst ba || !ba.beqIgnoringMetadata bb then none else
      some (.app m1 (.app m2 cmp (.intConst m2 ca)) (.intConst m1 cb), [])
    | _ => none

/-- `lo ≤ x ∧ x < hi → false if hi ≤ lo`, and `lo ≤ x ∧ x ≤ hi → false if ¬(lo ≤ hi)`, for
    integer literals `lo` and `hi`. Example: `0 ≤ k ∧ k < 0 → false`. -/
def emptyRangeRule : CondRule IntEnv where
  name := "int-empty-range"
  heads ie := ie.bool.isConn .And
  apply ie e := match ie.bool.conn? e with
    | some (.bin .and (.app m1 (.app m2 le@(.op _ o1 _) lo) x)
        (.app _ (.app _ (.op _ o2 _) x') hi)) => do
      if !x.beqIgnoringMetadata x' then none else
      let _ ← intLit? lo
      let _ ← intLit? hi
      match ie.ops.get? o1.name, ie.ops.get? o2.name with
      | some .Le, some .Lt => some (boolLit false, [.app m1 (.app m2 le hi) lo])
      | some .Le, some .Le => some (boolLit false, [mkNot (.app m1 (.app m2 le lo) hi)])
      | _, _ => none
    | _ => none

/-- The rules of the integer theory, in the order they are tried. -/
def integerRules : List (CondRule IntEnv) := [offsetCmpRule, emptyRangeRule]

/-! ## Evaluation -/

/-- The functions of a table that have a concrete evaluator. -/
structure EvalEnv where
  /-- The function table. -/
  functions : Lambda.Factory CoreLParams
  /-- The names of the functions with a concrete evaluator. -/
  evaluable : Std.HashSet String := {}

/-- The functions of `F` with a concrete evaluator. -/
def EvalEnv.ofFactory (F : Lambda.Factory CoreLParams) : EvalEnv :=
  { functions := F
    evaluable := F.toArray.foldl (init := {}) fun s f =>
      if f.concreteEval.isSome then s.insert f.name.name else s }

/-- Whether the evaluator of `fn` is meant for the arguments `args`: all are values, or the
    argument the function's attributes name is a constructor application or a value. -/
def evaluableOn (F : Lambda.Factory CoreLParams) (fn : LFunc CoreLParams)
    (args : List Expression.Expr) : Bool :=
  let at? (idx : Option Nat) (p : Expression.Expr → Bool) : Bool :=
    match idx with
    | some i => (args[i]?.map p).getD false
    | none => false
  args.all (LExpr.isValue F) ||
    at? (Strata.DL.Util.FuncAttr.findEvalIfConstr fn.attr) (LExpr.isConstrApp F) ||
    at? (Strata.DL.Util.FuncAttr.findEvalIfValue fn.attr) (LExpr.isValue F)

/-- `f(a₁, …, aₙ) → r` when the concrete evaluator of `f` gives `r` on the arguments, which
    are values (or, as `f`'s attributes say, a constructor application or a value where the
    evaluator needs one). The result is checked: the operator is annotated with an instance of
    its signature, the application has no loose bound variable, `r` type checks against the
    function table (`LExpr.typeCheckWith`: its operators agree with their signatures and it
    has the application's type), and every free variable of `r`, with its annotation, is one
    of the arguments'. Example: `str.concat("a", "b") → "ab"`. -/
def evalRule : CondRule EvalEnv where
  name := "evaluate"
  heads ev := opHead ev.evaluable.contains
  apply ev e := do
    let (opE, args, fn) ← ev.functions.callOfLFunc e
    let ceval ← fn.concreteEval
    if !evaluableOn ev.functions fn args || !opConsistent ev.functions opE then none else
    let r ← ceval e.metadata opE.opTy? args
    if r.beqIgnoringMetadata e then none else
    let ty ← LExpr.typeCheck [] e
    if LExpr.typeCheckWith ev.functions [] r != some ty then none else
    let argVars := args.flatMap LExpr.freeVars
    if !(LExpr.freeVars r).all (argVars.contains ·) then none else
    some (r, [])

/-- The rule of the evaluation theory. -/
def evaluationRules : List (CondRule EvalEnv) := [evalRule]

/-! ## Building the environment -/

/-- What the theories know about a program. -/
structure Theories where
  /-- The Boolean theory's connectives. -/
  bool : BoolEnv
  /-- The datatype theory's testers, selectors and constructors. -/
  dt : DatatypeEnv
  /-- The map theory's operators. -/
  maps : MapEnv
  /-- The sequence theory's operators. -/
  seqs : SeqEnv
  /-- The integer theory's operators. -/
  ints : IntEnv
  /-- The evaluation theory's functions. -/
  eval : EvalEnv

/-- The rules of all theories, in the order they are tried: Boolean, equality, datatypes,
    maps, sequences, integers, evaluation. -/
def allRules : List (CondRule Theories) :=
  booleanRules.map (·.lift Theories.bool) ++
  equalityRules.map (·.lift fun _ => ()) ++
  datatypeRules.map (·.lift Theories.dt) ++
  mapRules.map (·.lift Theories.maps) ++
  sequenceRules.map (·.lift Theories.seqs) ++
  integerRules.map (·.lift Theories.ints) ++
  evaluationRules.map (·.lift Theories.eval)

/-- The theories' knowledge of the function table `F` with the datatypes `dts`. -/
def Theories.ofFactory (F : Lambda.Factory CoreLParams) (dts : List (LDatatype Unit)) :
    Theories :=
  let bool := BoolEnv.ofFactory F
  { bool, dt := DatatypeEnv.ofFactory F dts, maps := MapEnv.ofFactory F,
    seqs := SeqEnv.ofFactory F, ints := IntEnv.ofFactory F bool, eval := EvalEnv.ofFactory F }

/-- Whether `F` has the operators the rules build, `¬ ∧ ∨ ⇒` and integer `+`, as Core's
    functions with their signatures. -/
def buildsOk (F : Lambda.Factory CoreLParams) (th : Theories) : Bool :=
  th.bool.connectives.get? "Bool.Not" == some .Not &&
  th.bool.connectives.get? "Bool.And" == some .And &&
  th.bool.connectives.get? "Bool.Or" == some .Or &&
  th.bool.connectives.get? "Bool.Implies" == some .Implies &&
  th.ints.ops.get? "Int.Add" == some .Add &&
  [boolNotOp, boolAndOp, boolOrOp, boolImpliesOp, intAddOp].all (opConsistent F)

/-- The engine's environment for the function table `F` with the datatypes `dts`. -/
def Env.ofFactory (F : Lambda.Factory CoreLParams) (dts : List (LDatatype Unit)) :
    Env Theories :=
  let th := Theories.ofFactory F dts
  Env.build F th.bool.connectives th allRules (buildsOk F th)

end -- public section

end Core.ContextualRewrite
