/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DL.SMT.Factory
import Strata.DL.SMT.Op
import Strata.DL.SMT.Solver
import Strata.DL.SMT.Term
import Strata.DL.SMT.TermType
import Std.Data.HashMap

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Encoder.lean)
This differs from Cedar's implementation in that we save the problem to a string instead of piping it to the solver
as we construct the problem.

This file defines the encoder, which translates a list of boolean Terms
into a list of SMT assertions. Term encoding is trusted.

 We will use the following type representations for primitive types:
 * `TermType.bool`:     builtin SMT `Bool` type
 * `TermType.int`:      builtin SMT `Int` type
 * `TermType.string`:   builtin SMT `String` type
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
  terms : Std.HashMap Term String
  types : Std.HashMap TermType String
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

def encodeType (ty : TermType) : EncoderM String := do
  if let (.some enc) := (← get).types.get? ty then return enc
  let enc ←
    match ty with
    | .bool             => return "Bool"
    | .int              => return "Int"
    | .string           => return "String"
    | .bitvec n         => return s!"(_ BitVec {n})"
    | .option oty       => return s!"(Option {← encodeType oty})"
    | .constr id targs  =>
      -- let targs' ← targs.mapM (fun t => encodeType t)
      let targs' ← go targs
      let targs' := Std.Format.joinSep targs' f!" "
      if targs.isEmpty then return id else return s!"({id} {targs'})"
  -- modifyGet λ state => (enc, {state with types := state.types.insert ty enc})
  where go (ts : List TermType) : EncoderM (List String) := do
  match ts with
  | [] => return []
  | t1 :: trest => do
    let t1' ← encodeType t1
    let trest' ← go trest
    return (t1' :: trest')

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

def declareVar (v : TermVar) (tyEnc : String) : EncoderM String := do
  let id := (termId (← termNum))
  comment (reprStr v.id)
  declareConst id tyEnc
  return id

def defineTerm (inBinder : Bool) (tyEnc tEnc : String) : EncoderM String := do
  if inBinder
  then return tEnc
  else do
    let id := termId (← termNum)
    defineFun id [] tyEnc tEnc
    return id

def defineTermBound := defineTerm True
def defineTermUnbound := defineTerm False

def defineSet (tyEnc : String) (tEncs : List String) : EncoderM String := do
  defineTermUnbound tyEnc (tEncs.foldl (λ acc t => s!"(set.insert {t} {acc})") s!"(as set.empty {tyEnc})")

def defineRecord (tyEnc : String) (tEncs : List String) : EncoderM String := do
  defineTermUnbound tyEnc s!"({tyEnc} {String.intercalate " " tEncs})"

def encodeUF (uf : UF) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let args ← uf.args.mapM (fun vt => encodeType vt.ty)
  declareFun id args (← encodeType uf.out)
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

 def encodeOp : Op → String
  | .eq            => "="
  | .zero_extend n => s!"(_ zero_extend {n})"
  | .option.get    => "val"
  | op             => op.mkName

def defineApp (inBinder : Bool) (tyEnc : String) (op : Op) (tEncs : List String) (_ts : List Term): EncoderM String := do
  let args := String.intercalate " " tEncs
  match op with
  | .uf f          =>
    if f.args.isEmpty then
      -- 0-ary function (i.e., a constant); shouldn't add parentheses here.
      defineTerm inBinder tyEnc s!"{← encodeUF f}"
    else
      defineTerm inBinder tyEnc s!"({← encodeUF f} {args})"
  | _              => defineTerm inBinder tyEnc s!"({encodeOp op} {args})"

def defineAll (inBinder : Bool) (xEnc : String) (tyEnc : String) (tEnc : String) : EncoderM String :=
  defineTerm inBinder "Bool" s!"(forall (({xEnc} {tyEnc})) {tEnc})"

def defineExist (inBinder : Bool) (xEnc : String) (tyEnc : String) (tEnc : String) : EncoderM String :=
  defineTerm inBinder "Bool" s!"(exists (({xEnc} {tyEnc})) {tEnc})"

def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

def encodeTerm (inBinder : Bool) (t : Term) : EncoderM String := do
  if let (.some enc) := (← get).terms.get? t then return enc
  let tyEnc ← encodeType t.typeOf
  let enc ←
    match t with
    | .var v            => if v.isBound then pure v.id else declareVar v tyEnc
    | .prim p           =>
      match p with
      | .bool b         => return if b then "true" else "false"
      | .int i          => return encodeInt i
      | .bitvec bv      => return encodeBitVec bv
      | .string s       => return encodeString s
    | .none _           => defineTerm inBinder tyEnc s!"(as none {tyEnc})"
    | .some t₁          => defineTerm inBinder tyEnc s!"(some {← encodeTerm inBinder t₁})"
    | .app .bvnego [t] .bool =>
      -- don't encode bvnego itself, for compatibility with older CVC5 (bvnego was
      -- introduced in CVC5 1.1.2)
      -- this rewrite is done in the encoder and is thus trusted
      match t.typeOf with
      | .bitvec n =>
        -- more fancy and possibly more optimized, but hard to prove termination:
        -- encodeTerm (Factory.eq t (BitVec.intMin n))
        defineApp inBinder tyEnc .eq [← encodeTerm inBinder t, encodeBitVec (BitVec.intMin n)] [t, BitVec.intMin n]
      | _ =>
        -- we could put anything here and be sound, because `bvnego` should only be
        -- applied to Terms of type .bitvec
        return "false"
    | .app op ts _         => defineApp inBinder tyEnc op (← mapM₁ ts (λ ⟨tᵢ, _⟩ => encodeTerm inBinder tᵢ)) ts
    | .quant .all x ty t   => defineAll inBinder x (← encodeType ty) (← encodeTerm True t)
    | .quant .exist x ty t => defineExist inBinder x (← encodeType ty) (← encodeTerm True t)
  if inBinder && !t.isFreeVar
  then pure enc
  else modifyGet λ state => (enc, {state with terms := state.terms.insert t enc})

def encodeFunction (uf : UF) (body : Term) : EncoderM String := do
  if let (.some enc) := (← get).ufs.get? uf then return enc
  let id := ufId (← ufNum)
  comment uf.id
  let ids ← uf.args.mapM (fun vt => pure vt.id)
  let args ← uf.args.mapM (fun vt => encodeType vt.ty)
  defineFun id (ids.zip args) (← encodeType uf.out) (← encodeTerm true body)
  modifyGet λ state => (id, {state with ufs := state.ufs.insert uf id})

/-- A utility for debugging. -/
def termToString (e : Term) : IO String := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let _ ← ((Encoder.encodeTerm False e).run EncoderState.init).run solver
  let contents ← b.get
  if h: String.validateUTF8 contents.data
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
    Solver.assert id

end Encoder
namespace Strata.SMT
