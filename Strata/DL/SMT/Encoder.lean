/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.DDMTransform.Translate
public import Strata.DL.SMT.Factory
public import Strata.DL.SMT.Op
public import Strata.Util.Name
public import Strata.DL.SMT.Solver
public import Strata.DL.SMT.Term
public import Strata.DL.SMT.TermType
import Std.Data.HashMap

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
   - **UF → abbreviated name cache** (`ufs`): Maps uninterpreted functions to
     their abbreviated identifiers (e.g., `$__f.0`, `$__f.1`).

The Encoder works purely with `Term` values. The `SolverM` layer handles all
string conversion and caching when emitting commands.

Deduplication of common subexpressions is handled by the Core-level ANF
encoder (`ANFEncoder.lean`), which runs as a pipeline phase before SMT
encoding. This keeps the SMT encoder simple and close to a 1-1 translation.

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

structure EncoderState where
  /-- Maps a `UF` to its abbreviated SMT identifier (e.g., `$__f.0`, `$__f.1`). -/
  ufs   : Std.HashMap UF String

def EncoderState.init : EncoderState where
  ufs := {}

@[expose] abbrev EncoderM (α) := StateT EncoderState SolverM α


namespace Encoder

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

/-- Sanitize a name for use in SMT-LIB. Symbols starting with `@` or `.` are
    reserved in SMT-LIB and rejected by z3 even when pipe-quoted. Prefix such
    names with `$` to make them valid simple symbols. -/
def sanitizeSmtName (name : String) : String :=
  if name.isEmpty then name
  else
    let first := name.front
    if first == '@' || first == '.' then "$" ++ name else name

/-- The `$__` prefix is reserved for internal use and cannot appear in user
    identifiers. The `.` after `t`/`f` prevents collision with
    evaluation-generated names (which use `@N` suffixes). -/
def termId (n : Nat)                    : String := s!"$__t.{n}"
def ufId (n : Nat)                      : String := s!"$__f.{n}"

def ufNum   : EncoderM Nat := do return (← get).ufs.size

def declareType (id : String) (mks : List String) : EncoderM String := do
  let constrs := mks.map fun name => SMTConstructor.mk name []
  declareDatatype id [] constrs
  return id

def defineSet (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  -- Build: (set.insert tN ... (set.insert t2 (set.insert t1 (as set.empty ty))))
  let empty : Term := .app (.datatype_op .constructor "set.empty") [] ty
  return tEncs.foldl (fun acc t => Term.app (.uf ⟨"set.insert", [⟨"x", t.typeOf⟩, ⟨"s", ty⟩], ty⟩) [t, acc] ty) empty

def defineRecord (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  return .app (.datatype_op .constructor ty.mkName) tEncs ty

def encodeUF (uf : UF) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  -- Check for name clashes with already-encoded UFs and reserved keywords, disambiguate
  let baseName := sanitizeSmtName uf.id
  let existingNames := (← get).ufs.toList.map (·.2)
  let usedNames := Std.HashSet.ofList (existingNames ++ smtReservedKeywords)
  let id := Strata.Name.findUnique baseName 1 usedNames
  comment uf.id
  let argTys := uf.args.map (fun vt => vt.ty)
  Solver.declareFun id argTys uf.out
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

def defineApp (ty : TermType) (op : Op) (tEncs : List Term) : EncoderM Term := do
  match op with
  | .uf f =>
    let ufName ← encodeUF f
    let ufRef : UF := { id := ufName, args := f.args, out := f.out }
    return .app (.uf ufRef) tEncs ty
  | _ =>
    return .app op tEncs ty

def extractTriggerGroup : Term -> List Term
| .app .triggers ts .trigger => ts
| e => [e]

def extractTriggers : Term -> List (List Term)
| .app .triggers ts .trigger => ts.map extractTriggerGroup
| e => [[e]]

/-- Every term in `extractTriggerGroup t` has `sizeOf ≤ sizeOf t`. -/
private theorem extractTriggerGroup_sizeOf (t ti : Term) (h : ti ∈ extractTriggerGroup t) :
    sizeOf ti ≤ sizeOf t := by
  unfold extractTriggerGroup at h
  split at h
  · have := List.sizeOf_lt_of_mem h; simp_all; omega
  · simp_all

/-- Every term nested in `extractTriggers t` has `sizeOf ≤ sizeOf t`. -/
theorem extractTriggers_sizeOf (t : Term) (ts : List Term) (ti : Term)
    (hts : ts ∈ extractTriggers t) (hti : ti ∈ ts) :
    sizeOf ti ≤ sizeOf t := by
  unfold extractTriggers at hts
  split at hts
  · rw [List.mem_map] at hts
    obtain ⟨t_elem, h_mem, h_eq⟩ := hts
    subst h_eq
    have h1 := extractTriggerGroup_sizeOf t_elem ti hti
    have h2 := List.sizeOf_lt_of_mem h_mem
    simp_all; omega
  · simp_all

-- Helper function for quantifier generation
def defineQuantifierHelper (qk : QuantifierKind) (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term := do
  let tr : Term := match trEncs with
    | [] => .app .triggers [] .trigger  -- empty trigger
    | groups =>
      -- Build trigger term from encoded trigger groups
      let triggerTerms := groups.map fun group =>
        .app .triggers group .trigger
      .app .triggers triggerTerms .trigger
  return .quant qk args tr bodyEnc

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
      let trExprs := if Factory.isSimpleTrigger tr then [] else extractTriggers tr
      let trEncs ← mapM₁ trExprs (fun ⟨ts, _⟩ => mapM₁ ts (fun ⟨ti, _⟩ => encodeTerm ti))
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
    | -- Trigger case: ti ∈ ts, ts ∈ trExprs, trExprs from extractTriggers tr
      -- Grab the membership hypotheses via ‹›, inline the let-binding
      -- (trExprs is definitionally the if-then-else), split, and apply our lemma.
      add_mem_size_lemmas
      have hmem : _ ∈ (if Factory.isSimpleTrigger tr then ([] : List (List Term)) else extractTriggers tr) := ‹_ ∈ trExprs›
      split at hmem
      · simp at hmem
      · have := extractTriggers_sizeOf tr _ _ hmem ‹_ ∈ _›
        simp_all; omega

def encodeFunction (uf : UF) (body : Term) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let argPairs := uf.args.map (fun vt => (vt.id, vt.ty))
  let bodyEnc ← encodeTerm body
  Solver.defineFunTerm id argPairs uf.out bodyEnc
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

/-- A utility for debugging. -/
def termToString (e : Term) : IO String := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let _ ← ((Encoder.encodeTerm e).run EncoderState.init).run solver
  let contents ← b.get
  if h: contents.data.IsValidUTF8
  then pure (String.fromUTF8 contents.data h)
  else pure "Converting SMT Term to bytes produced an invalid UTF-8 sequence."

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
  let (termEncs, _) ← ts.mapM encodeTerm |>.run EncoderState.init
  for t in termEncs do
    Solver.assert t

end Encoder

end

namespace Strata.SMT
