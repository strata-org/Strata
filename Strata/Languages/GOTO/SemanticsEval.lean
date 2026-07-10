/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.GOTO.Semantics
import Strata.Util.Tactics

/-!
# Concrete Expression Evaluator for GOTO Expressions

This file defines a concrete evaluator for the GOTO expression AST (`Expr`),
instantiating the abstract `ExprEval` parameter from `Semantics.lean`.

## Scope

Covers the expression forms produced by Strata's Lambda-to-GOTO translation
(`LambdaToCProverGOTO.lean`):

### Fully handled
- **Nullary**: `symbol` (variable lookup), `constant` (literal parsing)
- **Unary**: `Not`, `UnaryMinus` (integer), `Typecast` (bool↔int, int↔bv, bv↔bv)
- **Binary**: arithmetic (`Div`, `Mod`, `Minus`; integer), comparison (`Lt`,
  `Le`, `Gt`, `Ge`; integer), equality (`Equal`, `NotEqual`; structural, any
  value), logical (`Implies`), map (`Index`)
- **Ternary**: `ite` (if-then-else), `with` (map update)
- **Multiary**: `And`, `Or`, `Plus` (integer), `Mult` (integer)

### Not handled (returns `none`)
- **Side effects**: `Nondet`, `Assign` (handled at instruction level)
- **Function application**: `functionApplication` (uninterpreted)
- **`Old`**: handled by `concreteEval₂` (two-state evaluator)
- **Quantifiers**: `Forall`, `Exists` (specification-only)
- **Bitvector arithmetic/comparison/negation** (`Plus`, `Mult`, `Minus`, `Div`,
  `Mod`, `UnaryMinus`, `Lt`/`Le`/`Gt`/`Ge`): rejected pending width
  normalization. Applying the integer operation to the stored `Int` without
  wrapping modulo `2^w` (and without a signed/unsigned distinction) would be
  unsound BV semantics, so BV operands return `none` rather than a subtly-wrong
  result. Bitvector `constant`s, `Typecast`s, and structural `Equal`/`NotEqual`
  are still handled.
- **Bitvector bit-ops**: `Shl`, `Ashr`, `Lshr`, `Bitand`, `Bitor`, `Bitxor`,
  `Concatenation`, `Extractbits`
- **Real arithmetic**: `rational` values are parsed but arithmetic/comparison
  operations on reals are not yet implemented (returns `none`)

## TODO
- [ ] Bitvector width normalization (wrap results modulo `2^w`, track
      signedness), then re-enable BV arithmetic/comparison/negation
- [ ] Bitvector bit-level operations (width-aware)
- [ ] Real arithmetic (rational operations on `rational`)
- [ ] Prove correspondence with Lambda expression evaluation
-/

namespace CProverGOTO.Semantics

open CProverGOTO

public section

/-! ## Constant Parsing -/

/-- Smart constructor for bitvector values: normalize the stored integer to the
    canonical bit-pattern representative in `[0, 2^w)` (via Euclidean `n.emod 2^w`,
    which stays non-negative for a positive divisor — unlike `%`/`Int.mod`, whose
    truncated division would leave `(-1) % 256 = -1`). Storing a canonical value
    makes structural equality (`==`) on `Value.bv` sound — e.g. `mkBv 8 256 = mkBv 8 0`
    and `mkBv 8 (-1) = mkBv 8 255` — which is what `Equal`/`NotEqual` rely on.
    (Mapping the pattern to a signed range `[-(2^(w-1)), 2^(w-1))` for display is
    deferred to the width-normalization TODO; the bit pattern is what matters for
    equality.) -/
def mkBv (w : Nat) (n : Int) : Value :=
  .bv w (n.emod (2 ^ w : Int))

/-- Parse a GOTO constant string into a Value, given its type. -/
def parseConstant (val : String) (ty : Ty) : Option Value :=
  match ty.id with
  | .primitive .bool =>
    if val == "true" then some (.bool true)
    else if val == "false" then some (.bool false)
    else none
  | .primitive .integer => val.toInt?.map .int
  | .primitive .string => some (.string val)
  | .primitive .real => val.toInt?.map (fun n => .rational n 1)
  | .bitVector (.signedbv w) => val.toInt?.map (mkBv w)
  | .bitVector (.unsignedbv w) => val.toInt?.map (mkBv w)
  | _ => none

/-- Type cast between values. -/
def typeCast (v : Value) (targetTy : Ty) : Option Value :=
  match v, targetTy.id with
  | .bool b, .primitive .integer => some (.int (if b then 1 else 0))
  | .int n, .primitive .bool => some (.bool (n != 0))
  | .bv _ n, .bitVector (.signedbv w) => some (mkBv w n)
  | .bv _ n, .bitVector (.unsignedbv w) => some (mkBv w n)
  | .int n, .bitVector (.signedbv w) => some (mkBv w n)
  | .int n, .bitVector (.unsignedbv w) => some (mkBv w n)
  | _, _ => none

/-! ## Concrete Evaluator -/

/-- Core expression-evaluation logic. Both the single-state evaluator
    (`concreteEval`) and the two-state evaluator (`concreteEval₂`) are thin
    wrappers around this ONE recursive definition, so they cannot drift apart.

    `oldStore` selects the mode:
    - `none` — single-state: `old()` is unsupported and returns `none`.
    - `some σ_old` — two-state: `old(inner)` evaluates `inner` in the pre-state
      `σ_old` (staying in two-state mode), so `old()` is handled at ANY nesting
      depth, not just at the top level.

    Recursion is structural over the `Expr` operand tree — each recursive call
    is on an operand of `e`, and `term_by_mem` discharges the `sizeOf` decrease
    — so this is a total function rather than `partial`. -/
def evalCore (oldStore : Option Store) (σ : Store) (e : Expr) :
    Option Value :=
  match e.id, _: e.operands with
  -- `old()`: two-state only (see the mode note above).
  | .unary .Old, [inner] =>
    match oldStore with
    | some σ_old => evalCore (some σ_old) σ_old inner
    | none => none

  -- Nullary
  | .nullary (.symbol name), [] => σ name
  | .nullary (.constant val), [] => parseConstant val e.type
  | .nullary .nil, [] => some .undefined

  -- Unary
  | .unary .Not, [op] => do
    let .bool b ← evalCore oldStore σ op | none
    some (.bool !b)
  | .unary .UnaryMinus, [op] => do
    match ← evalCore oldStore σ op with
    | .int n => some (.int (-n))
    | _ => none
  | .unary .Typecast, [op] => do
    let v ← evalCore oldStore σ op
    typeCast v e.type

  -- Binary arithmetic (integer-only; bitvector operands rejected pending width
  -- normalization). `Div`/`Mod` reject a zero divisor with `none`: CBMC treats
  -- division by zero as undefined behavior, whereas Lean's `Int.div`/`Int.mod`
  -- are total and would silently yield `0`, masking the UB.
  | .binary .Div, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => if b == 0 then none else some (.int (a / b))
    | _, _ => none
  | .binary .Mod, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => if b == 0 then none else some (.int (a % b))
    | _, _ => none
  | .binary .Minus, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => some (.int (a - b))
    | _, _ => none

  -- Binary comparison (integer-only)
  | .binary .Lt, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => some (.bool (a < b))
    | _, _ => none
  | .binary .Le, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => some (.bool (a ≤ b))
    | _, _ => none
  | .binary .Gt, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => some (.bool (a > b))
    | _, _ => none
  | .binary .Ge, [l, r] => do
    match ← evalCore oldStore σ l, ← evalCore oldStore σ r with
    | .int a, .int b => some (.bool (a ≥ b))
    | _, _ => none
  | .binary .Equal, [l, r] => do
    some (.bool ((← evalCore oldStore σ l) == (← evalCore oldStore σ r)))
  | .binary .NotEqual, [l, r] => do
    some (.bool ((← evalCore oldStore σ l) != (← evalCore oldStore σ r)))

  -- Binary logical
  | .binary .Implies, [l, r] => do
    let .bool a ← evalCore oldStore σ l | none
    let .bool b ← evalCore oldStore σ r | none
    some (.bool (!a || b))

  -- Map/array operations
  | .binary .Index, [arr, idx] => do
    let .array elems ← evalCore oldStore σ arr | none
    let .int i ← evalCore oldStore σ idx | none
    if i < 0 then none else elems[i.toNat]?

  -- Ternary
  | .ternary .ite, [c, t, el] => do
    let .bool b ← evalCore oldStore σ c | none
    if b then evalCore oldStore σ t else evalCore oldStore σ el
  | .ternary .«with», [arr, idx, val] => do
    let .array elems ← evalCore oldStore σ arr | none
    let .int i ← evalCore oldStore σ idx | none
    let v ← evalCore oldStore σ val
    if i < 0 || i.toNat ≥ elems.length then none else
    some (.array (elems.set i.toNat v))

  -- Multiary. `attach` carries each operand's list membership so the recursive
  -- call inside the (pure) `.map` has its `sizeOf` decrease discharged by
  -- `term_by_mem`; `.mapM id` then sequences the resulting `Option`s.
  | .multiary .And, ops => do
    let vals : List Value ← (ops.attach.map (fun ⟨op, _⟩ => evalCore oldStore σ op)).mapM id
    let bs ← vals.mapM (fun | .bool b => some b | _ => none)
    some (.bool (bs.all id))
  | .multiary .Or, ops => do
    let vals : List Value ← (ops.attach.map (fun ⟨op, _⟩ => evalCore oldStore σ op)).mapM id
    let bs ← vals.mapM (fun | .bool b => some b | _ => none)
    some (.bool (bs.any id))
  -- Multiary arithmetic is integer-only: an empty operand list is the
  -- additive/multiplicative identity as an `.int`, a non-empty list must be all
  -- `.int`. Bitvector operands are rejected (`none`) as with the binary ops.
  | .multiary .Plus, ops => do
    let vals : List Value ← (ops.attach.map (fun ⟨op, _⟩ => evalCore oldStore σ op)).mapM id
    match vals with
    | [] => some (.int 0)
    | (.int _) :: _ => do
      let ns ← vals.mapM (fun | .int n => some n | _ => none)
      some (.int (ns.foldl (· + ·) 0))
    | _ => none
  | .multiary .Mult, ops => do
    let vals : List Value ← (ops.attach.map (fun ⟨op, _⟩ => evalCore oldStore σ op)).mapM id
    match vals with
    | [] => some (.int 1)
    | (.int _) :: _ => do
      let ns ← vals.mapM (fun | .int n => some n | _ => none)
      some (.int (ns.foldl (· * ·) 1))
    | _ => none

  -- Unsupported
  | _, _ => none
  termination_by (SizeOf.sizeOf e)
  decreasing_by all_goals (cases e; term_by_mem)

/-- Single-state concrete expression evaluator for GOTO expressions
    (`old()` unsupported). Total: see `evalCore`. -/
def concreteEval : ExprEval := fun σ e => evalCore none σ e

/-- Two-state concrete evaluator that handles `old()` expressions at any depth:
    `old(e)` evaluates `e` in `σ_old`; everything else uses `σ_cur`. A thin
    wrapper over `evalCore` in two-state mode. -/
def concreteEval₂ : ExprEval₂ := fun σ_old σ_cur e =>
  evalCore (some σ_old) σ_cur e

end -- public section

end CProverGOTO.Semantics
