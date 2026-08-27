/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Solver
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.SMT.DDMTransform.Parse
import Strata.DL.SMT.Factory
import Strata.Util.Name
import Strata.Util.Tactics

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Encoder.lean)

This file defines the encoder, which translates a list of boolean Terms
into a list of SMT assertions. Term encoding is trusted.

## Architecture

The encoding pipeline has two layers:

1. **Solver layer** (`SolverM`): A stateful monad that wraps the solver process
   and caches `Term → SMT-LIB string` and `TermType → SMT-LIB string`
   conversions. All string formatting lives in the Solver layer.

2. **Encoder layer** (`EncoderM`): Sits on top of `SolverM` and translates
   `Term` values to SMT-LIB commands:
   - `functions`: Maps functions to their abbreviated identifiers in SMT (e.g., `f.0`, `f.1`).
   - `isFunUninterp`: Stores whether a function has a body
   - `usedNames`: Every emitted SMT-LIB identifier
     is routed through `Strata.Name.findUnique` against this set, guaranteeing
     global uniqueness without relying on naming conventions.

The Encoder works purely with `Term` values. The `SolverM` layer handles all
string conversion and caching when emitting commands.

Deduplication of common subexpressions is handled by the Core-level
common-subexpression-elimination pass (`CommonSubexprElim.lean`), which runs as
a pipeline phase before SMT encoding. This keeps the SMT encoder simple and
close to a 1-1 translation.

 We will use the following type representations for primitive types:
 * `TermType.bool`:     builtin SMT `Bool` type
 * `TermType.int`:      builtin SMT `Int` type
 * `TermType.string`:   builtin SMT `String` type
 * `TermType.regex`:    builtin SMT `RegLan` type
 * `TermType.bitvec n`: builtin SMT `(_ BitVec n)` type

 We will represent non-primitive types as SMT algebraic datypes:
 * `TermType.option T`: a parameterized SMT algebraic datatype of the same name,
   and with the constructors `(some (val T))` and `(none)`. For each constructor
   argument, SMTLib introduces a corresponding (total) selector function. We
   will translate `Term.some` nodes in the Term language as applications of the
   `val` selector function.

 Similarly to types and attributes, all uninterpreted functions, variables, and
 Terms are mapped to their SMT encoding that conforms to the SMTLib syntax. We
 keep track of these mappings to ensure that each Term construct is translated
 to its SMT encoding exactly once.  This translation invariant is necessary for
 correctness in the case of UF names and variable names.
-/

namespace Strata.SMT

open Solver

public section

/-- SMT-LIB reserved keywords that should not be used as variable names.
    Includes command names, logical connectives, sort names, and theory
    function symbols that cvc5 disallows shadowing. -/
def smtReservedKeywords : List String :=
  -- SMT-LIB reserved words from the DDM parser
  let parserKeywords := _root_.Strata.reservedKeywords.map (·.2)
  -- Additional keywords not in the parser list
  parserKeywords ++
   ["true", "false", "Int", "Bool", "Real", "Array", "BitVec",
   -- Symbols from SMT. Note: this must be synchronized with Strata's internal SMT solver which has a denylist of
   -- names of variables/UFs/sorts.
   -- Core theory symbols
   "abs", "and", "distinct", "/", "=", ">", ">=", "ite", "=>",
   "div", "is_int", "<", "<=", "-", "mod", "*", "not", "or", "+",
   "to_int", "to_real", "xor",
   -- Nonlinear arithmetic theory symbols
   "exp", "sin", "cos", "tan", "sqrt", "pi",
   -- String theory symbols
   "str.at", "str.++", "str.contains", "str.from_code", "str.from_int",
   "str.in_re", "str.indexof", "str.is_digit", "str.<=", "str.len",
   "str.<", "str.prefixof", "str.replace", "str.substr", "str.suffixof",
   "str.to_code", "str.to_int", "str.to_re",
   -- Regex theory symbols
   "re.*", "re.+", "re.opt", "re.++", "re.union", "re.inter", "re.diff",
   "re.comp", "re.loop", "re.^", "re.range", "re.none", "re.all",
   "re.allchar",
   -- Array theory symbols
   "select", "store"]

/-- Pre-computed set of SMT reserved keywords for O(1) lookup. -/
def smtReservedKeywordsSet : Std.HashSet String :=
  Std.HashSet.ofList smtReservedKeywords

structure EncoderState where
  /-- Maps a `UF` to its abbreviated SMT identifier (e.g., `f.0`, `f.1`).
      Holds every function emitted so far, whether as an uninterpreted
      `declare-fun` or an interpreted `define-fun`; use `isFunUninterp` to
      distinguish the two. -/
  functions : Std.HashMap UF String
  /-- For each emitted function (same keys as `functions`), records whether it
      was emitted as an uninterpreted `declare-fun` (`true`) or an interpreted
      `define-fun` (`false`). Lets callers detect the unsound case where a
      function is first referenced (declared uninterpreted) and only later
      reached as a definition. -/
  isFunUninterp : Std.HashMap UF Bool
  /-- Every SMT-LIB identifier emitted so far. All emit sites route through
      `Strata.Name.findUnique` against this set, guaranteeing global uniqueness
      without relying on naming conventions. -/
  usedNames : Std.HashSet String

def EncoderState.init : EncoderState where
  functions := {}
  isFunUninterp := {}
  usedNames := smtReservedKeywordsSet

/-- Create an encoder state pre-populated with names already emitted to the
    solver (e.g. sort and datatype names declared before encoding begins). -/
def EncoderState.initWithNames (names : Std.HashSet String) : EncoderState where
  functions := {}
  isFunUninterp := {}
  usedNames := names.union smtReservedKeywordsSet

@[expose] abbrev EncoderM (α) := StateT EncoderState SolverM α


namespace Encoder

/-- Sanitize a name for use in SMT-LIB. Symbols starting with `@` or `.` are
    reserved in SMT-LIB and rejected by z3 even when pipe-quoted. Prefix such
    names with `$` to make them valid simple symbols. -/
def sanitizeSmtName (name : String) : String :=
  if name.isEmpty then name
  else
    let first := name.front
    if first == '@' || first == '.' then "$" ++ name else name

/-- Base name for internally generated UF identifiers. Correctness is enforced
    by the `usedNames` registry which disambiguates via `@N` suffixes on
    collision. -/
def ufId (n : Nat)                      : String := s!"f.{n}"

def ufNum   : EncoderM Nat := do return (← get).functions.size

/-- Allocate a globally unique SMT-LIB identifier. Checks the `usedNames`
    registry (and SMT reserved keywords) for collisions, disambiguates via
    `@N` suffixes, registers the result, and returns it. -/
def uniquify (baseName : String) : EncoderM String := do
  let id := Strata.Name.findUnique baseName 1 (← get).usedNames
  modify fun s => { s with usedNames := s.usedNames.insert id }
  return id

def declareType (id : String) (mks : List String) : EncoderM String := do
  let uniqueId ← uniquify id
  let constrs ← mks.mapM fun name => do
    let uniqueName ← uniquify name
    return SMTConstructor.mk uniqueName []
  declareDatatype uniqueId [] constrs
  return uniqueId

def defineSet (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  -- Build: (set.insert tN ... (set.insert t2 (set.insert t1 (as set.empty ty))))
  let empty : Term := .app (.datatype_op .constructor "set.empty") [] ty
  return tEncs.foldl (fun acc t => Term.app (.uf ⟨"set.insert", [t.typeOf, ty], ty⟩) [t, acc] ty) empty

def defineRecord (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  return .app (.datatype_op .constructor ty.mkName) tEncs ty

/-- Register a managed name (a program variable's `declare-fun`/`define-fun`)
    in the encoder state, so later `encodeUF` calls reuse the raw name
    instead of declaring and uniquifying their own. -/
def seedManagedName (estate : EncoderState) (uf : UF) : EncoderState :=
  { estate with
    functions := estate.functions.insert uf uf.id
    isFunUninterp := estate.isFunUninterp.insert uf false
    usedNames := estate.usedNames.insert uf.id }

def encodeUF (uf : UF) : EncoderM String := do
  if let (.some enc) := (← get).functions.get? uf then return enc
  let baseName := sanitizeSmtName uf.id
  let id ← uniquify baseName
  comment uf.id
  Solver.declareFun id uf.args uf.out
  modifyGet λ state => (id, {state with
    functions := state.functions.insert uf id
    isFunUninterp := state.isFunUninterp.insert uf true})

def defineApp (ty : TermType) (op : Op) (tEncs : List Term) : EncoderM Term := do
  match op with
  | .uf f =>
    let ufName ← encodeUF f
    let ufRef : UF := { id := ufName, args := f.args, out := f.out }
    return .app (.uf ufRef) tEncs ty
  | _ =>
    return .app op tEncs ty

-- Helper function for quantifier generation
def defineQuantifierHelper (qk : QuantifierKind) (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term := do
  return .quant qk args trEncs bodyEnc

def defineMultiAll (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper .all args trEncs bodyEnc

def defineMultiExist (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper .exist args trEncs bodyEnc

-- Convenience wrappers for single-variable quantifiers
def defineAll (x : String) (xty : TermType) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper .all [⟨x, xty⟩] trEncs bodyEnc

def defineExist (x : String) (xty : TermType) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper .exist [⟨x, xty⟩] trEncs bodyEnc

def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

def encodeTerm (t : Term) : EncoderM Term := do
  let ty := t.typeOf
  let enc ←
    match t with
    | .var _            => return t
    | .prim _           => return t
    | .none _           => return t
    | .some t₁          =>
      let t₁Enc ← encodeTerm t₁
      return .some t₁Enc
    | .app .re_allchar [] .regex => return t
    | .app .re_all     [] .regex => return t
    | .app .re_none    [] .regex => return t
    | .app .bvnego [inner] .bool =>
      match inner.typeOf with
      | .bitvec n =>
        let innerEnc ← encodeTerm inner
        let minVal : Term := .prim (.bitvec (BitVec.intMin n))
        defineApp ty .eq [innerEnc, minVal]
      | _ =>
        return Term.bool false
    | .app op ts _         => defineApp ty op (← mapM₁ ts (λ ⟨tᵢ, _⟩ => encodeTerm tᵢ))
    | .quant qk qargs tr body =>
      let trEncs ← mapM₁ tr (fun ⟨ts, _⟩ => mapM₁ ts (fun ⟨ti, _⟩ => encodeTerm ti))
      let bodyEnc ← encodeTerm body
      match qk, qargs with
      | .all, [⟨x, xty⟩] => defineAll x xty trEncs bodyEnc
      | .all, _ => defineMultiAll qargs trEncs bodyEnc
      | .exist, [⟨x, xty⟩] => defineExist x xty trEncs bodyEnc
      | .exist, _ => defineMultiExist qargs trEncs bodyEnc
  pure enc
termination_by sizeOf t
decreasing_by
  all_goals first
    | term_by_mem
    | -- Trigger case: ti ∈ ts, ts ∈ tr (a direct field of `.quant`).
      add_mem_size_lemmas
      have h1 := List.sizeOf_lt_of_mem ‹_ ∈ tr›
      have h2 := List.sizeOf_lt_of_mem ‹_ ∈ _›
      simp_all; omega

def encodeFunctionDef (f : IF) : EncoderM String := do
  let uf := f.toUF
  if let (.some enc) := (← get).functions.get? uf then
    -- The function was already emitted.
    if ((← get).isFunUninterp.get? uf).getD false then
      throw (IO.userError s!"encodeFunctionDef: function '{uf.id}' was already \
                declared as uninterpreted before its definition was encoded.")
    else
      return enc
  let baseName := ufId (← ufNum)
  let id ← uniquify baseName
  comment uf.id
  let argPairs := f.args.map (fun v => (v.id, v.ty))
  let bodyEnc ← encodeTerm f.body
  Solver.defineFunTerm id argPairs uf.out bodyEnc
  modifyGet λ state => (id, {state with
    functions := state.functions.insert uf id
    isFunUninterp := state.isFunUninterp.insert uf false})

/-- A utility for debugging. -/
def termToString (e : Term) : IO String := do
  let (_, text, _) ← Solver.recordToString ((Encoder.encodeTerm e).run EncoderState.init)
  pure text

/--
Once you've generated `Asserts` with one of the functions in Verifier.lean, you
can use this function to encode them as SMTLib assertions.

To actually solve these SMTLib assertions, you want to combine this `encode`
action with other `SolverM` actions, such as `Solver.check-sat` at a minimum.

Then you can run any `SolverM` action `act` with `act |>.run solver`, where
`solver` is a `Solver` instance you can construct using functions in
Solver.lean.

-/
def encode (ts : List Term) : SolverM Unit := do
  Solver.setLogic "ALL"
  Solver.declareDatatype "Option" ["X"]
    [⟨"none", []⟩, ⟨"some", [("val", .constr "X" [])]⟩]
  let initState := EncoderState.initWithNames (Std.HashSet.ofList ["Option", "none", "some", "val"])
  let (termEncs, _) ← ts.mapM encodeTerm |>.run initState
  for t in termEncs do
    Solver.assert t

/-- Encode each axiom and assert it. -/
def encodeAxioms (axms : Array Term) : EncoderM Unit := do
  let ids ← axms.mapM fun ax => encodeTerm ax
  for id in ids do
    Solver.assert id

end Encoder

end

namespace Strata.SMT
