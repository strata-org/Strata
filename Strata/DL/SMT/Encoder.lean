/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.Factory
import Strata.DL.SMT.Op
import Strata.DL.SMT.Solver
import Strata.DL.SMT.Term
import Strata.DL.SMT.TermType
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

2. **Encoder layer** (`EncoderM`): Sits on top of `SolverM` and manages
   A-normal form decomposition purely in the `Term` domain:
   - **Term → abbreviated Term cache** (`terms`): Maps each `Term` to its
     abbreviated `Term.var` reference (e.g., a variable named `t0`, `t1`).
     Large terms are broken into small `define-fun` definitions with short
     names, and the Solver handles all `Term → String` conversion.
   - **UF → abbreviated name cache** (`ufs`): Maps uninterpreted functions to
     their abbreviated identifiers (e.g., `f0`, `f1`).

The Encoder works purely with `Term` values. The `SolverM` layer handles all
string conversion and caching when emitting commands.

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
 correctness in the case of UF names and variable
 names; and it is neccessary for compactness in the case of terms. In
 particular, the resulting SMT encoding will be in A-normal form (ANF): the body
 of every s-expression in the encoding consists of atomic subterms (identifiers
 or literals).
-/

namespace Strata.SMT

open Solver

structure EncoderState where
  /-- Maps a `Term` to its abbreviated `Term` (a `Term.var` with name like `t0`).
      This is a cache after converting terms to A-Normal From. -/
  terms : Std.HashMap Term Term
  /-- Maps a `UF` to its abbreviated SMT identifier (e.g., `f0`, `f1`). -/
  ufs   : Std.HashMap UF String

def EncoderState.init : EncoderState where
  terms := {}
  ufs := {}

abbrev EncoderM (α) := StateT EncoderState SolverM α


namespace Encoder

def termId (n : Nat)                    : String := s!"t{n}"
def ufId (n : Nat)                      : String := s!"f{n}"

def termNum : EncoderM Nat := do return (← get).terms.size
def ufNum   : EncoderM Nat := do return (← get).ufs.size

def declareType (id : String) (mks : List String) : EncoderM String := do
  declareDatatype id [] mks
  return id

/-- Emit a `define-fun` for a term in ANF. When not in a binder, emits a
    `define-fun` with the given body `Term` and returns a `Term.var` reference
    to the abbreviated name. When in a binder, just returns the body term. -/
def defineTerm (inBinder : Bool) (ty : TermType) (body : Term) : EncoderM Term := do
  if inBinder
  then return body
  else do
    let id := termId (← termNum)
    Solver.defineFunTerm id [] ty body
    return .var ⟨id, ty⟩

def defineTermBound := defineTerm True
def defineTermUnbound := defineTerm False

def defineSet (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  -- Build: (set.insert t1 (set.insert t2 ... (as set.empty ty)))
  let empty : Term := .app (.datatype_op .constructor "set.empty") [] ty
  let result := tEncs.foldl (fun acc t => Term.app (.uf ⟨"set.insert", [⟨"x", t.typeOf⟩, ⟨"s", ty⟩], ty⟩) [t, acc] ty) empty
  defineTermUnbound ty result

def defineRecord (ty : TermType) (tEncs : List Term) : EncoderM Term := do
  defineTermUnbound ty (.app (.datatype_op .constructor ty.mkName) tEncs ty)

def encodeUF (uf : UF) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let argTys := uf.args.map (fun vt => vt.ty)
  Solver.declareFun id argTys uf.out
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

def defineApp (inBinder : Bool) (ty : TermType) (op : Op) (tEncs : List Term) : EncoderM Term := do
  match op with
  | .uf f =>
    let ufName ← encodeUF f
    let ufRef : UF := { id := ufName, args := f.args, out := f.out }
    defineTerm inBinder ty (.app (.uf ufRef) tEncs ty)
  | _ =>
    defineTerm inBinder ty (.app op tEncs ty)

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
private theorem extractTriggers_sizeOf (t : Term) (ts : List Term) (ti : Term)
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
def defineQuantifierHelper (inBinder : Bool) (qk : QuantifierKind) (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term := do
  let tr : Term := match trEncs with
    | [] => .app .triggers [] .trigger  -- empty trigger
    | groups =>
      -- Build trigger term from encoded trigger groups
      let triggerTerms := groups.map fun group =>
        .app .triggers group .trigger
      .app .triggers triggerTerms .trigger
  defineTerm inBinder .bool (.quant qk args tr bodyEnc)

def defineMultiAll (inBinder : Bool) (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper inBinder .all args trEncs bodyEnc

def defineMultiExist (inBinder : Bool) (args : List TermVar) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper inBinder .exist args trEncs bodyEnc

-- Convenience wrappers for single-variable quantifiers
def defineAll (inBinder : Bool) (x : String) (xty : TermType) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper inBinder .all [⟨x, xty⟩] trEncs bodyEnc

def defineExist (inBinder : Bool) (x : String) (xty : TermType) (trEncs: List (List Term)) (bodyEnc : Term) : EncoderM Term :=
  defineQuantifierHelper inBinder .exist [⟨x, xty⟩] trEncs bodyEnc

def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

def encodeTerm (inBinder : Bool) (t : Term) : EncoderM Term := do
  if let (.some enc) := (← get).terms.get? t then return enc
  let ty := t.typeOf
  let enc ←
    match t with
    | .var _            => return t
    | .prim _           => return t
    | .none _           => defineTerm inBinder ty t
    | .some t₁          =>
      let t₁Enc ← encodeTerm inBinder t₁
      defineTerm inBinder ty (.some t₁Enc)
    | .app .re_allchar [] .regex => return t
    | .app .re_all     [] .regex => return t
    | .app .re_none    [] .regex => return t
    | .app .bvnego [inner] .bool =>
      match inner.typeOf with
      | .bitvec n =>
        let innerEnc ← encodeTerm inBinder inner
        let minVal : Term := .prim (.bitvec (BitVec.intMin n))
        defineApp inBinder ty .eq [innerEnc, minVal]
      | _ =>
        return Term.bool false
    | .app op ts _         => defineApp inBinder ty op (← mapM₁ ts (λ ⟨tᵢ, _⟩ => encodeTerm inBinder tᵢ))
    | .quant qk qargs tr body =>
      let trExprs := if Factory.isSimpleTrigger tr then [] else extractTriggers tr
      let trEncs ← mapM₁ trExprs (fun ⟨ts, _⟩ => mapM₁ ts (fun ⟨ti, _⟩ => encodeTerm True ti))
      let bodyEnc ← encodeTerm True body
      match qk, qargs with
      | .all, [⟨x, xty⟩] => defineAll inBinder x xty trEncs bodyEnc
      | .all, _ => defineMultiAll inBinder qargs trEncs bodyEnc
      | .exist, [⟨x, xty⟩] => defineExist inBinder x xty trEncs bodyEnc
      | .exist, _ => defineMultiExist inBinder qargs trEncs bodyEnc
  if inBinder
  then pure enc
  else modifyGet λ state => (enc, {state with terms := state.terms.insert t enc})
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
  let bodyEnc ← encodeTerm true body
  Solver.defineFunTerm id argPairs uf.out bodyEnc
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

/-- A utility for debugging. -/
def termToString (e : Term) : IO String := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let _ ← ((Encoder.encodeTerm False e).run EncoderState.init).run solver
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

Note that `encode` itself first resets the solver in order to define datatypes
etc.
-/
def encode (ts : List Term) : SolverM Unit := do
  Solver.reset
  Solver.setLogic "ALL"
  Solver.declareDatatype "Option" ["X"] ["(none)", "(some (val X))"]
  let (termEncs, _) ← ts.mapM (encodeTerm False) |>.run EncoderState.init
  for t in termEncs do
    Solver.assert t

end Encoder
namespace Strata.SMT
