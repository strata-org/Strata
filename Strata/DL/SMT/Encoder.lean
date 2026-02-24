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
   conversions. Core typed commands (`assert`, `defineFun`, `declareFun`,
   `declareConst`) accept `Term`/`TermType` values directly.

2. **Encoder layer** (`EncoderM`): Sits on top of `SolverM` and manages:
   - **Term → abbreviated name cache** (`terms`): Maps each `Term` to its
     abbreviated SMT identifier (e.g., `t0`, `t1`). This is the ANF
     decomposition: large terms are broken into small `define-fun` definitions
     with short names.
   - **TermType → SMT string cache** (`types`): Maps types to their SMT
     string representation for the encoder's own use.
   - **UF → abbreviated name cache** (`ufs`): Maps uninterpreted functions to
     their abbreviated identifiers (e.g., `f0`, `f1`).

The Encoder's job is purely to decompose a large SMT term into a sequence of
smaller `define-fun` commands using abbreviated names. The `SolverM` layer
handles the actual string conversion and caching.

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
  /-- Maps a `Term` to its abbreviated SMT identifier (e.g., `t0`, `t1`).
      This is the ANF decomposition cache. -/
  terms : Std.HashMap Term String
  /-- Maps a `TermType` to its SMT string representation (e.g., `Bool`, `Int`). -/
  types : Std.HashMap TermType String
  /-- Maps a `UF` to its abbreviated SMT identifier (e.g., `f0`, `f1`). -/
  ufs   : Std.HashMap UF String

def EncoderState.init : EncoderState where
  terms := {}
  types := {}
  ufs := {}

abbrev EncoderM (α) := StateT EncoderState SolverM α


namespace Encoder

def termId (n : Nat)                    : String := s!"t{n}"
def ufId (n : Nat)                      : String := s!"f{n}"
def enumId (E : String) (n : Nat)       : String := s!"{E}_m{n}"

def typeNum : EncoderM Nat := do return (← get).types.size
def termNum : EncoderM Nat := do return (← get).terms.size
def ufNum   : EncoderM Nat := do return (← get).ufs.size

def declareType (id : String) (mks : List String) : EncoderM String := do
  declareDatatype id [] mks
  return id

/-- Convert a `TermType` to its SMT-LIB string, delegating to `Solver.typeToSMTString`
    which uses the `SolverState` cache. -/
def encodeType (ty : TermType) : EncoderM String := do
  if let (.some enc) := (← get).types.get? ty then return enc
  Solver.typeToSMTString ty

/-
String printing has to be done carefully in the presence of
non-ASCII characters.  See the SMTLib standard for the details:
https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml. Here,
we're assuming ASCII strings for simplicity.
-/
def encodeString (s : String) : String :=
  s!"\"{s}\""

def encodeInt (i : Int) : String :=
  s!"{i}"

def encodeBitVec {n : Nat} (bv : _root_.BitVec n) : String :=
  s!"(_ bv{bv.toNat} {n})"

/--
A constant in the theory of unicode strings denoting the set of all strings of
length 1.
No enclosing parentheses should be used here.
-/
def encodeReAllChar : String :=
  s!"re.allchar"

/--
A constant in the theory of unicode strings denoting the set of all strings.
No enclosing parentheses should be used here.
-/
def encodeReAll : String :=
  s!"re.all"

/--
A constant in the theory of unicode strings denoting the empty set of strings.
No enclosing parentheses should be used here.
-/
def encodeReNone : String :=
  s!"re.none"

/-- Define a term in ANF. When not in a binder, emits a `define-fun` with the
    given `TermType` and returns the abbreviated id. When in a binder, just
    returns the expression string. -/
def defineTerm (inBinder : Bool) (ty : TermType) (tEnc : String) : EncoderM String := do
  if inBinder
  then return tEnc
  else do
    let id := termId (← termNum)
    Solver.defineFun id [] ty tEnc
    return id

def defineTermBound := defineTerm True
def defineTermUnbound := defineTerm False

def defineSet (ty : TermType) (tEncs : List String) : EncoderM String := do
  let tyEnc ← encodeType ty
  defineTermUnbound ty (tEncs.foldl (λ acc t => s!"(set.insert {t} {acc})") s!"(as set.empty {tyEnc})")

def defineRecord (ty : TermType) (tEncs : List String) : EncoderM String := do
  let tyEnc ← encodeType ty
  defineTermUnbound ty s!"({tyEnc} {String.intercalate " " tEncs})"

def encodeUF (uf : UF) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let argTys := uf.args.map (fun vt => vt.ty)
  Solver.declareFun id argTys uf.out
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

 def encodeOp : Op → String
  | .eq            => "="
  | .zero_extend n => s!"(_ zero_extend {n})"
  | .re_index n    => s!"(_ re.^ {n})"
  | .re_loop n₁ n₂ => s!"(_ re.loop {n₁} {n₂})"
  | .option_get    => "val"
  | op             => op.mkName

def extractTriggerGroup : Term -> List Term
| .app .triggers ts .trigger => ts
| e => [e]

def extractTriggers : Term -> List (List Term)
| .app .triggers ts .trigger => ts.map extractTriggerGroup
| e => [[e]]

def encodeTriggerGroup (trEncs : List String) : String :=
  s!":pattern ({String.intercalate " " trEncs})"

def encodeTriggers (trs : List (List String)) : String :=
  String.intercalate " " (trs.map encodeTriggerGroup)

def defineApp (inBinder : Bool) (ty : TermType) (op : Op) (tEncs : List String) (_ts : List Term): EncoderM String := do
  let tyEnc ← encodeType ty
  let args := String.intercalate " " tEncs
  match op with
  | .uf f          =>
    if f.args.isEmpty then
      defineTerm inBinder ty s!"{← encodeUF f}"
    else
      defineTerm inBinder ty s!"({← encodeUF f} {args})"
  | .datatype_op .constructor name =>
    if tEncs.isEmpty then
      defineTerm inBinder ty s!"(as {name} {tyEnc})"
    else
      defineTerm inBinder ty s!"((as {name} {tyEnc}) {args})"
  | .datatype_op _ _ =>
    defineTerm inBinder ty s!"({encodeOp op} {args})"
  | _ =>
    if tEncs.isEmpty then
      defineTerm inBinder ty s!"({encodeOp op})"
    else
      defineTerm inBinder ty s!"({encodeOp op} {args})"

-- Helper function for quantifier generation
def defineQuantifierHelper (inBinder : Bool) (quantKind : String) (varDecls : String) (trEncs: List (List String)) (tEnc : String) : EncoderM String :=
  defineTerm inBinder .bool $
    match trEncs with
    | [] =>
      s!"({quantKind} ({varDecls}) {tEnc})"
    | _ =>
      s!"({quantKind} ({varDecls}) (! {tEnc} {encodeTriggers trEncs}))"

def defineMultiAll (inBinder : Bool) (args : List TermVar) (trEncs: List (List String)) (tEnc : String) : EncoderM String := do
  let varDecls ← args.mapM (fun ⟨x, ty⟩ => do
    let tyEnc ← encodeType ty
    return s!"({x} {tyEnc})")
  let varDeclsStr := String.intercalate " " varDecls
  defineQuantifierHelper inBinder "forall" varDeclsStr trEncs tEnc

def defineMultiExist (inBinder : Bool) (args : List TermVar) (trEncs: List (List String)) (tEnc : String) : EncoderM String := do
  let varDecls ← args.mapM (fun ⟨x, ty⟩ => do
    let tyEnc ← encodeType ty
    return s!"({x} {tyEnc})")
  let varDeclsStr := String.intercalate " " varDecls
  defineQuantifierHelper inBinder "exists" varDeclsStr trEncs tEnc

-- Convenience wrappers for single-variable quantifiers - implemented in terms of helper
def defineAll (inBinder : Bool) (xEnc : String) (tyEnc : String) (trEncs: List (List String)) (tEnc : String) : EncoderM String :=
  defineQuantifierHelper inBinder "forall" s!"({xEnc} {tyEnc})" trEncs tEnc

def defineExist (inBinder : Bool) (xEnc : String) (tyEnc : String) (trEncs: List (List String)) (tEnc : String) : EncoderM String :=
  defineQuantifierHelper inBinder "exists" s!"({xEnc} {tyEnc})" trEncs tEnc

def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

partial
def encodeTerm (inBinder : Bool) (t : Term) : EncoderM String := do
  if let (.some enc) := (← get).terms.get? t then return enc
  let ty := t.typeOf
  let tyEnc ← encodeType ty
  let enc ←
    match t with
    | .var v            => return v.id
    | .prim _           =>
      -- Use the cached termToSMTString for primitives
      let s ← Solver.termToSMTString t
      return s
    | .none _           => defineTerm inBinder ty s!"(as none {tyEnc})"
    | .some t₁          => defineTerm inBinder ty s!"(some {← encodeTerm inBinder t₁})"
    | .app .re_allchar [] .regex => return encodeReAllChar
    | .app .re_all     [] .regex => return encodeReAll
    | .app .re_none    [] .regex => return encodeReNone
    | .app .bvnego [t] .bool =>
      match t.typeOf with
      | .bitvec n =>
        defineApp inBinder ty .eq [← encodeTerm inBinder t, encodeBitVec (BitVec.intMin n)] [t, BitVec.intMin n]
      | _ =>
        return "false"
    | .app op ts _         => defineApp inBinder ty op (← mapM₁ ts (λ ⟨tᵢ, _⟩ => encodeTerm inBinder tᵢ)) ts
    | .quant qk args tr t =>
      let trExprs := if Factory.isSimpleTrigger tr then [] else extractTriggers tr
      let trEncs ← mapM₁ trExprs (fun ⟨ts, _⟩ => mapM₁ ts (fun ⟨t, _⟩ => encodeTerm True t))
      match qk, args with
      | .all, [⟨x, xty⟩] => defineAll inBinder x (← encodeType xty) trEncs (← encodeTerm True t)
      | .all, _ => defineMultiAll inBinder args trEncs (← encodeTerm True t)
      | .exist, [⟨x, xty⟩] => defineExist inBinder x (← encodeType xty) trEncs (← encodeTerm True t)
      | .exist, _ => defineMultiExist inBinder args trEncs (← encodeTerm True t)
  if inBinder
  then pure enc
  else modifyGet λ state => (enc, {state with terms := state.terms.insert t enc})

def encodeFunction (uf : UF) (body : Term) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let argPairs := uf.args.map (fun vt => (vt.id, vt.ty))
  Solver.defineFun id argPairs uf.out (← encodeTerm true body)
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
  let (ids, _) ← ts.mapM (encodeTerm False) |>.run EncoderState.init
  for id in ids do
    Solver.assertId id

end Encoder
namespace Strata.SMT
