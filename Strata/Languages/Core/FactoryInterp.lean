/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import Strata.Util.RealProps
import Strata.DL.Lambda.Denote.LExprDenoteConsts

/-!
## A Sound Interpretation of `Core.Factory`

This module builds a concrete, consistent `Lambda.Interp Core.Factory` and the
witness `Nonempty (Lambda.Interp Core.Factory)`.

The primary entry points are:
- `Core.factoryInterp : Lambda.Interp Core.Factory`
- `Core.factoryInterp_interpConsistent` exposes its factory-consistency proof
- `Core.factoryInterp_axiomsSatisfied`: every axiom of `Core.Factory` holds in it, so the
  axioms are jointly satisfiable
- `Core.factory_axioms_wellTyped`: every axiom of `Core.Factory` is a well-typed closed
  Boolean formula, so the previous result applies to all of them
- `Core.factoryInterp_nonempty : Nonempty (Lambda.Interp Core.Factory)`
- `Core.RealsAsReal`: an operator interpretation gives the real operations their SMT-LIB
  meaning on `Strata.Util.Real`, and `Core.factoryInterp_realsAsReal` shows the concrete
  interpretation does

Implementation declarations live under `Core.FactoryInterpModel`.
-/

open Lambda

namespace Core

public section

/-- The sort `real → real → out` of a binary real operation. -/
@[match_pattern] abbrev realBinSort (out : LSort) : LSort :=
  .tcons "arrow" [.tcons "real" [], .tcons "arrow" [.tcons "real" [], out]]

namespace FactoryInterpModel

/-- Core's Lambda expression parameters. -/
abbrev T : LExprParams := Core.CoreLParams

/-- The carrier of each sort in the model. Primitive sorts, arrows, maps (functions)
and sequences (lists) are interpreted as by `SortDenote`, and a `Set a` is a
predicate. Every other type constructor is `Unit`. -/
@[expose] def Carrier : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Strata.Util.Real
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => Carrier a → Carrier b
  | .tcons "Map" [k, v]   => Carrier k → Carrier v
  | .tcons "Set" [a]      => Carrier a → Bool
  | .tcons "Sequence" [a] => List (Carrier a)
  | .tcons _ _            => Unit

/-- Type constructors are interpreted by their carriers. -/
@[expose] def tcInterp : TyConstrInterp := fun name args => Carrier (.tcons name args)

/-- Every sort denotes its carrier. The two differ definitionally only on sorts
whose head is unknown, such as the value of a type variable. -/
-- Not `private`: the exposed `toC` and `ofC` below unfold to it.
theorem sortDenote_eq_carrier (s : LSort) : SortDenote tcInterp s = Carrier s := by
  induction s using LSort.ind with
  | hbitvec n => rfl
  | htcons name args ih =>
    unfold SortDenote
    split
    all_goals (rename_i heq; cases heq)
    all_goals first
      | rfl
      | (rename_i a b
         show (SortDenote tcInterp a → SortDenote tcInterp b) = (Carrier a → Carrier b)
         rw [ih a (by simp), ih b (by simp)])
      | (rename_i a
         show List (SortDenote tcInterp a) = List (Carrier a)
         rw [ih a (by simp)])

/-- A default value of every carrier. -/
def Carrier.default (s : LSort) : Carrier s := by
  induction s using LSort.rec' with
  | hbitvec n => exact (0 : BitVec n)
  | htcons name args ih =>
    unfold Carrier
    split
    next => exact false
    next => exact (0 : Int)
    next => exact (0 : Strata.Util.Real)
    next => exact ""
    next n _ => exact (0 : BitVec n)
    next _ _ b heq => cases heq; exact fun _ => ih b (by simp)
    next _ _ v heq => cases heq; exact fun _ => ih v (by simp)
    next => exact fun _ => false
    next => exact []
    next => exact ()

instance (s : LSort) : Inhabited (Carrier s) := ⟨Carrier.default s⟩

/-- Every carrier is inhabited. -/
instance instAllInhab : TyConstrInterp.AllInhabited tcInterp :=
  ⟨fun name args => ⟨Carrier.default (.tcons name args)⟩⟩

/-- View a semantic value as an element of its carrier. -/
@[expose] def toC {s : LSort} (x : SortDenote tcInterp s) : Carrier s :=
  cast (sortDenote_eq_carrier s) x

/-- View an element of a carrier as a semantic value. -/
@[expose] def ofC {s : LSort} (x : Carrier s) : SortDenote tcInterp s :=
  cast (sortDenote_eq_carrier s).symm x

/-- `ofC` undoes `toC`. -/
@[simp] private theorem ofC_toC {s : LSort} (x : SortDenote tcInterp s) : ofC (toC x) = x := by
  simp [ofC, toC]

/-- `toC` undoes `ofC`. -/
@[simp] private theorem toC_ofC {s : LSort} (x : Carrier s) : toC (ofC x) = x := by
  simp [ofC, toC]

/-- `toC` is injective: two values are equal exactly when their carrier views are. -/
@[simp] private theorem toC_inj {s : LSort} (x y : SortDenote tcInterp s) : toC x = toC y ↔ x = y :=
  ⟨fun h => by simpa using congrArg ofC h, fun h => h ▸ rfl⟩

open Classical in
/-- Move an element between carriers, as the identity when the sorts agree.
The interpretations below take their sorts apart into independent pieces, and
use `coe` where the typing rules make two of those pieces equal. -/
@[expose] noncomputable def coe (a b : LSort) (x : Carrier a) : Carrier b :=
  if h : a = b then h ▸ x else Carrier.default b

/-- Moving an element to its own carrier leaves it unchanged. -/
@[simp] private theorem coe_self (a : LSort) (x : Carrier a) : coe a a x = x := by
  simp [coe]

/-- `coe a a` is the identity function. -/
@[simp] private theorem coe_self_fun (a : LSort) : coe a a = id := funext (coe_self a)

open Classical in
/-- Move a semantic value between sorts, as the identity when the sorts agree (`coe` on
semantic values rather than carriers). -/
@[expose] noncomputable def coeS (a b : LSort) (x : SortDenote tcInterp a) :
    SortDenote tcInterp b :=
  if h : a = b then h ▸ x else default

/-- Moving a semantic value to its own sort leaves it unchanged. -/
@[simp] private theorem coeS_self (a : LSort) (x : SortDenote tcInterp a) : coeS a a x = x := by
  simp [coeS]

/-- `coeS a a` is the identity function. -/
@[simp] private theorem coeS_self_fun (a : LSort) : coeS a a = id := funext (coeS_self a)

open Classical in
/-- Reify a primitive semantic value as a Core literal. A real that is not the image of a
rational has no literal and is reified as `0`. -/
@[expose] noncomputable def reifyAt : (s : LSort) → SortDenote tcInterp s → LExpr T.mono
  | .tcons "bool" [],   v => .const default (.boolConst v)
  | .tcons "int" [],    v => .const default (.intConst v)
  | .tcons "real" [],   v => .const default (.rationalConst
      (if h : ∃ r, Strata.Util.Real.ofRat r = v then Classical.choose h else 0))
  | .tcons "string" [], v => .const default (.strConst v)
  | .bitvec n,          v => .const default (.bitvecConst n v)
  | .tcons "arrow" [_, _], _ => .const default (.boolConst false)
  | .tcons _ _, _ => .const default (.boolConst false)

open Classical in
/-- The embedding of a rational is reified as its literal. -/
theorem reifyAt_ofRat (r : Rat) :
    reifyAt (.tcons "real" []) (Strata.Util.Real.ofRat r) = .const default (.rationalConst r) := by
  have h : ∃ r', Strata.Util.Real.ofRat r' = Strata.Util.Real.ofRat r := ⟨r, rfl⟩
  show LExpr.const (T := T.mono) default (.rationalConst
    (if h : ∃ r', Strata.Util.Real.ofRat r' = Strata.Util.Real.ofRat r then Classical.choose h
      else 0)) = _
  split
  · rename_i h'; rw [Strata.Util.Real.ofRat_inj.mp (Classical.choose_spec h')]
  · contradiction

/-- Decode a Core literal as a semantic value, defaulting for unsupported forms. -/
@[expose] def decodeAt : (s : LSort) → Option (LExpr T.mono) → SortDenote tcInterp s
  | .tcons "bool" [],   some (.const _ (.boolConst b)) => b
  | .tcons "int" [],    some (.const _ (.intConst i))  => i
  | .tcons "real" [],   some (.const _ (.rationalConst r)) => Strata.Util.Real.ofRat r
  | .tcons "string" [], some (.const _ (.strConst s)) => s
  | .bitvec n,          some (.const _ (.bitvecConst n' b)) =>
      if h : n = n' then h ▸ b else default
  | s, _ => (SortDenote.instInhabited s).default

/-- Lift a concrete evaluator to a curried semantic value at the requested sort. -/
@[expose] noncomputable def gatherEval
    (ceval : ConcreteEval T)
    (acc : List (LExpr T.mono)) : (s : LSort) → SortDenote tcInterp s
  | .tcons "arrow" [a, b] => fun (x : SortDenote tcInterp a) =>
      gatherEval ceval (acc ++ [reifyAt a x]) b
  | .tcons "bool" [] => decodeAt (.tcons "bool" []) (ceval default none acc)
  | .tcons "int" [] => decodeAt (.tcons "int" []) (ceval default none acc)
  | .tcons "real" [] => decodeAt (.tcons "real" []) (ceval default none acc)
  | .tcons "string" [] => decodeAt (.tcons "string" []) (ceval default none acc)
  | .bitvec n => decodeAt (.bitvec n) (ceval default none acc)
  | .tcons nm args => decodeAt (.tcons nm args) (ceval default none acc)

/-! Equations for `gatherEval` at the primitive output sorts. Lean cannot generate
`gatherEval`'s equation lemmas automatically, so we state the cases used below
directly. -/

theorem gatherEval_bool
    (ceval : ConcreteEval T)
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "bool" []) =
      decodeAt (.tcons "bool" []) (ceval default none acc) := rfl

theorem gatherEval_int
    (ceval : ConcreteEval T)
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "int" []) =
      decodeAt (.tcons "int" []) (ceval default none acc) := rfl

theorem gatherEval_string
    (ceval : ConcreteEval T)
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "string" []) =
      decodeAt (.tcons "string" []) (ceval default none acc) := rfl

theorem gatherEval_bitvec
    (ceval : ConcreteEval T)
    (acc : List (LExpr T.mono)) (n : Nat) :
    gatherEval ceval acc (.bitvec n) =
      decodeAt (.bitvec n) (ceval default none acc) := rfl

/-! ### Interpretation of the axiomatized operations

The functions of `Core.Factory` without a concrete evaluator are interpreted by
`axiomOp`, which gives `Map`, `Set` and `Sequence` operations the meaning their
axioms describe on the carriers above, and the real operations their meaning in
the SMT-LIB theory of reals, on `Strata.Util.Real` (every other one is a default value).
Division by zero is `0` here; `Core.RealsAsReal` leaves it unconstrained, as
SMT-LIB does. -/

/-- The element at index `i` of a sequence, or a default value out of range. -/
@[expose] noncomputable def seqGet (a b : LSort) (s : List (SortDenote tcInterp a)) (i : Int) :
    SortDenote tcInterp b :=
  if h : 0 ≤ i ∧ i.toNat < s.length then coeS a b (s[i.toNat]'h.2) else default

/-- The unchecked sequence operations have the meaning of their checked counterparts;
their axioms are the same up to the name. -/
@[expose] def checkedName : String → String
  | "Sequence.select!" => "Sequence.select"
  | "Sequence.update!" => "Sequence.update"
  | "Sequence.take!" => "Sequence.take"
  | "Sequence.drop!" => "Sequence.drop"
  | n => n

/-- The semantic values of a `Sequence a`. -/
abbrev SeqC (a : LSort) : Type := List (SortDenote tcInterp a)
/-- The carrier of a `Set a`. -/
abbrev SetC (a : LSort) : Type := Carrier a → Bool
/-- The semantic values of a `Map k v`. -/
abbrev MapC (k v : LSort) : Type := SortDenote tcInterp k → SortDenote tcInterp v

open Classical in
/-- Interpretation of the operations of `Core.Factory` that are only axiomatized,
by name (after `checkedName`) and sort. -/
@[expose] noncomputable def axiomOpAt : (name : String) → (s : LSort) → SortDenote tcInterp s
  | "mapConst", .tcons "arrow" [v, .tcons "Map" [_, v']] =>
    fun (d : SortDenote tcInterp v) => (fun _ => coeS v v' d : MapC _ v')
  | "select", .tcons "arrow" [.tcons "Map" [k, v], .tcons "arrow" [k', v']] =>
    fun (mm : MapC k v) (x : SortDenote tcInterp k') => coeS v v' (mm (coeS k' k x))
  | "update", .tcons "arrow" [.tcons "Map" [k, v],
      .tcons "arrow" [k1, .tcons "arrow" [v1, .tcons "Map" [k2, v2]]]] =>
    fun (mm : MapC k v) (x : SortDenote tcInterp k1) (y : SortDenote tcInterp v1) =>
      (fun z => if coeS k2 k1 z = x then coeS v1 v2 y else coeS v v2 (mm (coeS k2 k z))
        : MapC k2 v2)
  | "Set.empty", .tcons "Set" [a] => (fun _ => false : SetC a)
  | "Set.contains", .tcons "arrow" [.tcons "Set" [a], .tcons "arrow" [a', .tcons "bool" []]] =>
    fun (st : SetC a) (x : SortDenote tcInterp a') => st (coe a' a (toC x))
  | "Set.insert", .tcons "arrow" [.tcons "Set" [a], .tcons "arrow" [a', .tcons "Set" [a'']]] =>
    fun (st : SetC a) (x : SortDenote tcInterp a') =>
      (fun y => decide (coe a'' a' y = toC x) || st (coe a'' a y) : SetC a'')
  | "Set.remove", .tcons "arrow" [.tcons "Set" [a], .tcons "arrow" [a', .tcons "Set" [a'']]] =>
    fun (st : SetC a) (x : SortDenote tcInterp a') =>
      (fun y => !decide (coe a'' a' y = toC x) && st (coe a'' a y) : SetC a'')
  | "Set.union", .tcons "arrow" [.tcons "Set" [a],
      .tcons "arrow" [.tcons "Set" [a'], .tcons "Set" [a'']]] =>
    fun (st : SetC a) (t : SetC a') => (fun y => st (coe a'' a y) || t (coe a'' a' y) : SetC a'')
  | "Set.intersect", .tcons "arrow" [.tcons "Set" [a],
      .tcons "arrow" [.tcons "Set" [a'], .tcons "Set" [a'']]] =>
    fun (st : SetC a) (t : SetC a') => (fun y => st (coe a'' a y) && t (coe a'' a' y) : SetC a'')
  | "Set.difference", .tcons "arrow" [.tcons "Set" [a],
      .tcons "arrow" [.tcons "Set" [a'], .tcons "Set" [a'']]] =>
    fun (st : SetC a) (t : SetC a') => (fun y => st (coe a'' a y) && !t (coe a'' a' y) : SetC a'')
  | "Sequence.length", .tcons "arrow" [.tcons "Sequence" [a], .tcons "int" []] =>
    fun (s : SeqC a) => (s.length : Int)
  | "Sequence.empty", .tcons "Sequence" [a] => ([] : SeqC a)
  | "Sequence.append", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [.tcons "Sequence" [a'], .tcons "Sequence" [a'']]] =>
    fun (s : SeqC a) (t : SeqC a') => ((s ++ t.map (coeS a' a)).map (coeS a a'') : SeqC a'')
  | "Sequence.select",
      .tcons "arrow" [.tcons "Sequence" [a], .tcons "arrow" [.tcons "int" [], b]] =>
    fun (s : SeqC a) (i : Int) => seqGet a b s i
  | "Sequence.build", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [a', .tcons "Sequence" [a'']]] =>
    fun (s : SeqC a) (v : SortDenote tcInterp a') =>
      ((s ++ [coeS a' a v]).map (coeS a a'') : SeqC a'')
  | "Sequence.update", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [.tcons "int" [], .tcons "arrow" [a', .tcons "Sequence" [a'']]]] =>
    fun (s : SeqC a) (i : Int) (v : SortDenote tcInterp a') =>
      ((if 0 ≤ i then s.set i.toNat (coeS a' a v) else s).map (coeS a a'') : SeqC a'')
  | "Sequence.contains", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [a', .tcons "bool" []]] =>
    fun (s : SeqC a) (v : SortDenote tcInterp a') =>
      decide (∃ i : Int, 0 ≤ i ∧ i < s.length ∧ seqGet a a' s i = v)
  | "Sequence.take", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [.tcons "int" [], .tcons "Sequence" [a']]] =>
    fun (s : SeqC a) (n : Int) => ((s.take n.toNat).map (coeS a a') : SeqC a')
  | "Sequence.drop", .tcons "arrow" [.tcons "Sequence" [a],
      .tcons "arrow" [.tcons "int" [], .tcons "Sequence" [a']]] =>
    fun (s : SeqC a) (n : Int) =>
      ((if 0 ≤ n then s.drop n.toNat
        else List.replicate (-n).toNat (default : SortDenote tcInterp a) ++ s).map
          (coeS a a') : SeqC a')
  | "Real.Add", realBinSort (.tcons "real" []) =>
    fun (x y : Strata.Util.Real) => x + y
  | "Real.Sub", realBinSort (.tcons "real" []) =>
    fun (x y : Strata.Util.Real) => x - y
  | "Real.Mul", realBinSort (.tcons "real" []) =>
    fun (x y : Strata.Util.Real) => x * y
  | "Real.Div", realBinSort (.tcons "real" []) =>
    fun (x y : Strata.Util.Real) => x / y
  | "Real.Neg", .tcons "arrow" [.tcons "real" [], .tcons "real" []] => fun (x : Strata.Util.Real) => -x
  | "Real.Lt", realBinSort (.tcons "bool" []) =>
    fun (x y : Strata.Util.Real) => decide (x < y)
  | "Real.Le", realBinSort (.tcons "bool" []) =>
    fun (x y : Strata.Util.Real) => decide (x ≤ y)
  | "Real.Gt", realBinSort (.tcons "bool" []) =>
    fun (x y : Strata.Util.Real) => decide (x > y)
  | "Real.Ge", realBinSort (.tcons "bool" []) =>
    fun (x y : Strata.Util.Real) => decide (x ≥ y)
  | _, s => (SortDenote.instInhabited s).default

/-- Interpretation of the operations of `Core.Factory` without a concrete evaluator. -/
@[expose] noncomputable def axiomOp (name : String) (s : LSort) : SortDenote tcInterp s :=
  axiomOpAt (checkedName name) s

/-- The operator interpretation: look up the factory function by name. If it has a
`concreteEval` and is monomorphic (an operation on primitive values), build its
denotation by reifying arguments, calling `concreteEval`, and decoding the result;
otherwise interpret it by `axiomOp`. The polymorphic functions with a `concreteEval`
are the `Map` and `Sequence` operations, which evaluate on literals (`polyLitOp`); their
arguments can be maps, which are not all literals, so their meaning is `axiomOp`'s,
which their evaluators agree with. -/
@[expose] noncomputable def opInterp : OpInterp tcInterp :=
  fun name s =>
    match Core.Factory.get? name with
    | none => (SortDenote.instInhabited s).default
    | some func =>
      match func.concreteEval with
      | none => axiomOp name s
      | some ceval => if func.typeArgs.isEmpty then gatherEval ceval [] s else axiomOp name s

/-- No function in the built-in `Core.Factory` has a body. -/
private theorem all_bodies_none : ∀ f ∈ Core.Factory.toArray, f.body = none := by
  intro f hf
  have hmem : f ∈ Core.WFFactoryArray.map (·.func) :=
    Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) hf
  obtain ⟨wf, hwf, rfl⟩ := Array.mem_map.mp hmem
  rw [Array.mem_def] at hwf
  simp only [Core.WFFactoryArray, Array.toList_appendList] at hwf
  have h := (List.all_eq_true (p := fun wf => wf.func.body.isNone)).mp ?_ wf hwf
  · simpa using h
  · decide +kernel

/-- No function in the built-in `Core.Factory` is a constructor. -/
private theorem all_not_constr : ∀ f ∈ Core.Factory.toArray, f.isConstr = false := by
  intro f hf
  have hmem : f ∈ Core.WFFactoryArray.map (·.func) :=
    Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) hf
  obtain ⟨wf, hwf, rfl⟩ := Array.mem_map.mp hmem
  rw [Array.mem_def] at hwf
  simp only [Core.WFFactoryArray, Array.toList_appendList] at hwf
  have h := (List.all_eq_true (p := fun wf => !wf.func.isConstr)).mp ?_ wf hwf
  · simpa using h
  · decide +kernel

/-- A function looked up by name belongs to `Core.Factory`'s underlying array. -/
private theorem get_mem (name : String) (p : name ∈ Core.Factory) :
    Core.Factory.get name p ∈ Core.Factory.toArray := by
  simp only [Lambda.Factory.get]; exact Array.getElem_mem _

/-- Bodies half of `Factory.InterpConsistent`: vacuous, since no factory
function has a body. -/
private theorem bodies_consistent :
    ∀ (f : String), (hf : f ∈ Core.Factory) → ∀ body, (Core.Factory[f]).body = some body →
      LFunc.InterpConsistentBody tcInterp opInterp (Core.Factory[f]) body := by
  intro f hf body hbody
  have hnone : (Core.Factory[f]).body = none := all_bodies_none _ (get_mem f hf)
  rw [hnone] at hbody
  exact absurd hbody (by simp)

/-! ### Primitive bridge typeclasses

These capture, for a closed primitive input/output type `ty` with Lean carrier
`V`, exactly the reify/decode/denote facts needed to prove `concreteEval`
consistency generically over `unaryOp`/`binaryOp`. Facts are phrased directly
at `LMonoTy.substTyVars vt ty` (the type `denote` naturally produces), so the
generic proofs need no type casts. -/

/-- Input-side primitive bridge: how a closed input type's `concreteEval`
decoder (`cevalIn`) relates to `reifyAt`/`denote`. -/
class InPrim (inTy : LMonoTy) (InV : outParam Type) where
  /-- The literal decoder for this type (`LambdaLeanType.cevalTy`). -/
  cevalIn : LExpr T.mono → Option InV
  /-- `inTy` is closed, so type substitution leaves it unchanged. -/
  closed : inTy.freeVars = []
  /-- If `x` decodes to `a`, then reifying its denotation decodes to `a` too. -/
  reify_ceval : ∀ (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
      (x : LExpr T.mono) (h : LExpr.HasTypeA [] x inTy) (a : InV),
      cevalIn x = some a →
      cevalIn (reifyAt (LMonoTy.substTyVars vt inTy)
        (LExpr.denote tcInterp opInterp fvarVal vt .nil x inTy h)) = some a

/-- Output-side primitive bridge: how a closed output type's constant builder
(`mkOut`) relates to `decodeAt`/`denote`/`gatherEval`. -/
class OutPrim (outTy : LMonoTy) (OutV : outParam Type) where
  /-- The literal builder for this type (`LambdaLeanType.mkConst`). -/
  mkOut : T.Metadata → OutV → LExpr T.mono
  /-- `outTy` is closed, so type substitution leaves it unchanged. -/
  closed : outTy.freeVars = []
  /-- `outTy`'s sort is not an arrow, so `gatherEval` decodes directly. -/
  gather_eq : ∀ (vt : TyVarVal) ceval acc,
      gatherEval ceval acc (LMonoTy.substTyVars vt outTy)
        = decodeAt (LMonoTy.substTyVars vt outTy) (ceval default none acc)
  /-- Denoting a built constant equals decoding it (metadata-insensitive). -/
  denote_decode : ∀ (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
      (md md' : T.Metadata) (w : OutV) (h : LExpr.HasTypeA [] (mkOut md w) outTy),
      LExpr.denote tcInterp opInterp fvarVal vt .nil (mkOut md w) outTy h
        = decodeAt (LMonoTy.substTyVars vt outTy) (some (mkOut md' w))

/-- Generic `concreteEval` consistency for a unary op over primitive types; `guard` is checked
on the argument. -/
private theorem unaryOp_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type}
    (func : LFunc T)
    (ceval : ConcreteEval T)
    (hin : (List.map Prod.snd func.inputs) = [inTy])
    (hout : func.output = outTy)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    [ip : InPrim inTy InV] [op : OutPrim outTy OutV]
    (f : InV → OutV) (guard : InV → Bool)
    (hmono : func.typeArgs = [])
    (hbeh : ∀ md opTy x, ceval md opTy [x] =
      (match InPrim.cevalIn (inTy := inTy) x with
       | some a => if guard a then some (OutPrim.mkOut (outTy := outTy) md (f a)) else none
       | _ => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr
  simp only []
  intro heval h_args h_result
  have hci : LMonoTy.subst tySubst inTy = inTy :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [ip.closed]; simp)
  have hco : LMonoTy.subst tySubst outTy = outTy :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [op.closed]; simp)
  have hIT : (List.map (LMonoTy.subst tySubst) (List.map Prod.snd func.inputs)) = [inTy] := by
    rw [hin]; simp [hci]
  have hOT : LMonoTy.subst tySubst func.output = outTy := by rw [hout]; exact hco
  revert h_args h_result
  rw [hIT, hOT]
  intro h_args h_result
  cases h_args with
  | @cons a b as bs hx htail =>
    cases htail
    rw [hbeh md _ a] at heval
    cases hca : InPrim.cevalIn (inTy := inTy) a with
    | none => rw [hca] at heval; simp at heval
    | some av =>
      rw [hca] at heval
      simp only at heval
      split at heval
      · rename_i hg
        simp only [Option.some.injEq] at heval
        subst heval
        simp only [opInterp, hlook, hce, hmono, List.isEmpty_nil, ↓reduceIte, denoteArgs]
        show LExpr.denote tcInterp opInterp fvarVal vt HList.nil (OutPrim.mkOut outTy md (f av)) outTy h_result
            = gatherEval ceval [reifyAt (LMonoTy.substTyVars vt inTy)
                (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a inTy hx)] (LMonoTy.substTyVars vt outTy)
        rw [OutPrim.gather_eq, hbeh default none, InPrim.reify_ceval fvarVal vt a hx av hca]
        rw [OutPrim.denote_decode fvarVal vt md default (f av) h_result]
        simp only [hg, ite_true]
      · simp at heval

/-- Generic `concreteEval` consistency for a binary op over primitive types.
Both inputs share type `inTy`; `guard` is checked on the second argument. -/
private theorem binaryOp_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type}
    (func : LFunc T)
    (ceval : ConcreteEval T)
    (hin : (List.map Prod.snd func.inputs) = [inTy, inTy])
    (hout : func.output = outTy)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    [ip : InPrim inTy InV] [opr : OutPrim outTy OutV]
    (g : InV → InV → OutV) (guard : InV → Bool)
    (hmono : func.typeArgs = [])
    (hbeh : ∀ md opTy x y, ceval md opTy [x, y] =
      (match InPrim.cevalIn (inTy := inTy) x, InPrim.cevalIn (inTy := inTy) y with
       | some a, some b => if guard b then some (OutPrim.mkOut (outTy := outTy) md (g a b)) else none
       | _, _ => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr
  simp only []
  intro heval h_args h_result
  have hci : LMonoTy.subst tySubst inTy = inTy :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [ip.closed]; simp)
  have hco : LMonoTy.subst tySubst outTy = outTy :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [opr.closed]; simp)
  have hIT : (List.map (LMonoTy.subst tySubst) (List.map Prod.snd func.inputs)) = [inTy, inTy] := by
    rw [hin]; simp [hci]
  have hOT : LMonoTy.subst tySubst func.output = outTy := by rw [hout]; exact hco
  revert h_args h_result
  rw [hIT, hOT]
  intro h_args h_result
  cases h_args with
  | @cons a b as bs hx htail =>
    cases htail with
    | @cons a2 b2 as2 bs2 hy htail2 =>
      cases htail2
      rw [hbeh md _ a a2] at heval
      cases hca : InPrim.cevalIn (inTy := inTy) a with
      | none => rw [hca] at heval; simp at heval
      | some av =>
        cases hcb : InPrim.cevalIn (inTy := inTy) a2 with
        | none => rw [hca, hcb] at heval; simp at heval
        | some bv =>
          rw [hca, hcb] at heval
          simp only at heval
          split at heval
          · rename_i hg
            simp only [Option.some.injEq] at heval
            subst heval
            simp only [opInterp, hlook, hce, hmono, List.isEmpty_nil, ↓reduceIte, denoteArgs]
            show LExpr.denote tcInterp opInterp fvarVal vt HList.nil
                  (OutPrim.mkOut outTy md (g av bv)) outTy h_result
                = gatherEval ceval
                    [reifyAt (LMonoTy.substTyVars vt inTy)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a inTy hx),
                     reifyAt (LMonoTy.substTyVars vt inTy)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a2 inTy hy)]
                    (LMonoTy.substTyVars vt outTy)
            rw [OutPrim.gather_eq, hbeh default none,
                InPrim.reify_ceval fvarVal vt a hx av hca,
                InPrim.reify_ceval fvarVal vt a2 hy bv hcb,
                OutPrim.denote_decode fvarVal vt md default (g av bv) h_result]
            simp only [hg, ite_true]
          · simp at heval

/-- Generic `concreteEval` consistency for a binary op over primitive types whose inputs have
different types `inTy1` and `inTy2`; `guard` is checked on the second argument. -/
private theorem heteroBinaryOp_consistent
    {inTy1 inTy2 outTy : LMonoTy} {InV1 InV2 OutV : Type}
    (func : LFunc T)
    (ceval : ConcreteEval T)
    (hin : (List.map Prod.snd func.inputs) = [inTy1, inTy2])
    (hout : func.output = outTy)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    [ip1 : InPrim inTy1 InV1] [ip2 : InPrim inTy2 InV2] [opr : OutPrim outTy OutV]
    (g : InV1 → InV2 → OutV) (guard : InV2 → Bool)
    (hmono : func.typeArgs = [])
    (hbeh : ∀ md opTy x y, ceval md opTy [x, y] =
      (match InPrim.cevalIn (inTy := inTy1) x, InPrim.cevalIn (inTy := inTy2) y with
       | some a, some b => if guard b then some (OutPrim.mkOut (outTy := outTy) md (g a b)) else none
       | _, _ => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr
  simp only []
  intro heval h_args h_result
  have hci1 : LMonoTy.subst tySubst inTy1 = inTy1 :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [ip1.closed]; simp)
  have hci2 : LMonoTy.subst tySubst inTy2 = inTy2 :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [ip2.closed]; simp)
  have hco : LMonoTy.subst tySubst outTy = outTy :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [opr.closed]; simp)
  have hIT : (List.map (LMonoTy.subst tySubst) (List.map Prod.snd func.inputs)) = [inTy1, inTy2] := by
    rw [hin]; simp [hci1, hci2]
  have hOT : LMonoTy.subst tySubst func.output = outTy := by rw [hout]; exact hco
  revert h_args h_result
  rw [hIT, hOT]
  intro h_args h_result
  cases h_args with
  | @cons a b as bs hx htail =>
    cases htail with
    | @cons a2 b2 as2 bs2 hy htail2 =>
      cases htail2
      rw [hbeh md _ a a2] at heval
      cases hca : InPrim.cevalIn (inTy := inTy1) a with
      | none => rw [hca] at heval; simp at heval
      | some av =>
        cases hcb : InPrim.cevalIn (inTy := inTy2) a2 with
        | none => rw [hca, hcb] at heval; simp at heval
        | some bv =>
          rw [hca, hcb] at heval
          simp only at heval
          split at heval
          · rename_i hg
            simp only [Option.some.injEq] at heval
            subst heval
            simp only [opInterp, hlook, hce, hmono, List.isEmpty_nil, ↓reduceIte, denoteArgs]
            show LExpr.denote tcInterp opInterp fvarVal vt HList.nil
                  (OutPrim.mkOut outTy md (g av bv)) outTy h_result
                = gatherEval ceval
                    [reifyAt (LMonoTy.substTyVars vt inTy1)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a inTy1 hx),
                     reifyAt (LMonoTy.substTyVars vt inTy2)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a2 inTy2 hy)]
                    (LMonoTy.substTyVars vt outTy)
            rw [OutPrim.gather_eq, hbeh default none,
                InPrim.reify_ceval fvarVal vt a hx av hca,
                InPrim.reify_ceval fvarVal vt a2 hy bv hcb,
                OutPrim.denote_decode fvarVal vt md default (g av bv) h_result]
            simp only [hg, ite_true]
          · simp at heval

/-! ### Primitive bridge instances -/

/-- If `denoteBool` decodes an expression, it is the corresponding Boolean literal. -/
private theorem denoteBool_some (x : LExpr T.mono) (a : Bool)
    (h : LExpr.denoteBool x = some a) : ∃ m, x = LExpr.const m (LConst.boolConst a) := by
  cases x with
  | const m c => cases c <;> simp_all [LExpr.denoteBool]
  | op => simp [LExpr.denoteBool] at h
  | bvar => simp [LExpr.denoteBool] at h
  | fvar => simp [LExpr.denoteBool] at h
  | abs => simp [LExpr.denoteBool] at h
  | quant => simp [LExpr.denoteBool] at h
  | app => simp [LExpr.denoteBool] at h
  | ite => simp [LExpr.denoteBool] at h
  | eq => simp [LExpr.denoteBool] at h

instance : InPrim LMonoTy.bool Bool where
  cevalIn := LExpr.denoteBool
  closed := by decide
  reify_ceval := by
    intro fvarVal vt x h a hx
    obtain ⟨m, rfl⟩ := denoteBool_some x a hx
    simp only [LMonoTy.bool] at h ⊢
    rw [denote_boolConst tcInterp opInterp fvarVal vt .nil h]
    rfl

instance : OutPrim LMonoTy.bool Bool where
  mkOut := fun md w => .const md (.boolConst w)
  closed := by decide
  gather_eq := by intro vt ceval acc; exact gatherEval_bool ceval acc
  denote_decode := by
    intro fvarVal vt md md' w h
    simp only [LMonoTy.bool] at h ⊢
    rw [denote_boolConst tcInterp opInterp fvarVal vt .nil h]
    rfl

/-- `concreteEval` consistency for a short-circuiting Boolean connective (`shortCircuitOp`):
when the first operand is `absorb` the result is the constant `decided`, and otherwise it
is the second operand itself, which need not be a literal. In that second case the
interpretation decodes the reified denotation of the second operand, which is that
denotation again. -/
private theorem shortCircuit_consistent
    (func : LFunc T)
    (ceval : ConcreteEval T)
    (hin : (List.map Prod.snd func.inputs) = [LMonoTy.bool, LMonoTy.bool])
    (hout : func.output = LMonoTy.bool)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    (absorb decided : Bool)
    (hmono : func.typeArgs = [])
    (hbeh : ∀ md opTy x y, ceval md opTy [x, y] =
      (match InPrim.cevalIn (inTy := LMonoTy.bool) x with
       | some a =>
         if a == absorb then some (OutPrim.mkOut (outTy := LMonoTy.bool) md decided) else some y
       | none => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr
  simp only []
  intro heval h_args h_result
  have hb : LMonoTy.subst tySubst LMonoTy.bool = LMonoTy.bool :=
    LMonoTy.subst_no_relevant_keys _ _ (by rw [InPrim.closed (inTy := LMonoTy.bool)]; simp)
  have hIT : (List.map (LMonoTy.subst tySubst) (List.map Prod.snd func.inputs))
      = [LMonoTy.bool, LMonoTy.bool] := by
    rw [hin]; simp [hb]
  have hOT : LMonoTy.subst tySubst func.output = LMonoTy.bool := by rw [hout]; exact hb
  revert h_args h_result
  rw [hIT, hOT]
  intro h_args h_result
  cases h_args with
  | @cons a b as bs hx htail =>
    cases htail with
    | @cons a2 b2 as2 bs2 hy htail2 =>
      cases htail2
      rw [hbeh md _ a a2] at heval
      cases hca : InPrim.cevalIn (inTy := LMonoTy.bool) a with
      | none => rw [hca] at heval; simp at heval
      | some av =>
        rw [hca] at heval
        simp only [opInterp, hlook, hce, hmono, List.isEmpty_nil, ↓reduceIte, denoteArgs]
        show LExpr.denote tcInterp opInterp fvarVal vt HList.nil resultExpr LMonoTy.bool h_result
            = gatherEval ceval
                [reifyAt (LMonoTy.substTyVars vt LMonoTy.bool)
                    (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a LMonoTy.bool hx),
                 reifyAt (LMonoTy.substTyVars vt LMonoTy.bool)
                    (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a2 LMonoTy.bool hy)]
                (LMonoTy.substTyVars vt LMonoTy.bool)
        rw [OutPrim.gather_eq (outTy := LMonoTy.bool), hbeh default none,
            InPrim.reify_ceval fvarVal vt a hx av hca]
        simp only at heval ⊢
        cases hg : (av == absorb)
        · simp only [hg, Bool.false_eq_true, ite_false, Option.some.injEq] at heval ⊢
          subst heval
          rfl
        · simp only [hg, ite_true, Option.some.injEq] at heval ⊢
          subst heval
          exact OutPrim.denote_decode fvarVal vt md default decided h_result

/-- If `denoteInt` decodes an expression, it is the corresponding integer literal. -/
private theorem denoteInt_some (x : LExpr T.mono) (a : Int)
    (h : LExpr.denoteInt x = some a) : ∃ m, x = LExpr.const m (LConst.intConst a) := by
  cases x with
  | const m c => cases c <;> simp_all [LExpr.denoteInt]
  | op => simp [LExpr.denoteInt] at h
  | bvar => simp [LExpr.denoteInt] at h
  | fvar => simp [LExpr.denoteInt] at h
  | abs => simp [LExpr.denoteInt] at h
  | quant => simp [LExpr.denoteInt] at h
  | app => simp [LExpr.denoteInt] at h
  | ite => simp [LExpr.denoteInt] at h
  | eq => simp [LExpr.denoteInt] at h

instance : InPrim LMonoTy.int Int where
  cevalIn := LExpr.denoteInt
  closed := by decide
  reify_ceval := by
    intro fvarVal vt x h a hx
    obtain ⟨m, rfl⟩ := denoteInt_some x a hx
    simp only [LMonoTy.int] at h ⊢
    rw [denote_intConst tcInterp opInterp fvarVal vt .nil h]
    rfl

instance : OutPrim LMonoTy.int Int where
  mkOut := fun md w => .const md (.intConst w)
  closed := by decide
  gather_eq := by intro vt ceval acc; exact gatherEval_int ceval acc
  denote_decode := by
    intro fvarVal vt md md' w h
    simp only [LMonoTy.int] at h ⊢
    rw [denote_intConst tcInterp opInterp fvarVal vt .nil h]
    rfl

/-- If `denoteString` decodes an expression, it is the corresponding string literal. -/
private theorem denoteString_some (x : LExpr T.mono) (a : String)
    (h : LExpr.denoteString x = some a) : ∃ m, x = LExpr.const m (LConst.strConst a) := by
  cases x with
  | const m c => cases c <;> simp_all [LExpr.denoteString]
  | op => simp [LExpr.denoteString] at h
  | bvar => simp [LExpr.denoteString] at h
  | fvar => simp [LExpr.denoteString] at h
  | abs => simp [LExpr.denoteString] at h
  | quant => simp [LExpr.denoteString] at h
  | app => simp [LExpr.denoteString] at h
  | ite => simp [LExpr.denoteString] at h
  | eq => simp [LExpr.denoteString] at h

instance : InPrim LMonoTy.string String where
  cevalIn := LExpr.denoteString
  closed := by decide
  reify_ceval := by
    intro fvarVal vt x h a hx
    obtain ⟨m, rfl⟩ := denoteString_some x a hx
    rw [Lambda.denote_strConst (T := T) tcInterp opInterp fvarVal vt .nil h]
    rfl

instance : OutPrim LMonoTy.string String where
  mkOut := fun md w => .const md (.strConst w)
  closed := by decide
  gather_eq := by intro vt ceval acc; exact gatherEval_string ceval acc
  denote_decode := by
    intro fvarVal vt md md' w h
    rw [Lambda.denote_strConst (T := T) tcInterp opInterp fvarVal vt .nil h]
    rfl

/-- If `denoteBitVec n` decodes an expression, it is a width-`n` bitvector literal
    with the decoded value. -/
private theorem denoteBitVec_some (n : Nat) (x : LExpr T.mono) (a : BitVec n)
    (h : LExpr.denoteBitVec n x = some a) :
    ∃ m b, x = LExpr.const m (LConst.bitvecConst n b) ∧ BitVec.ofNat n b.toNat = a := by
  cases x with
  | const m c =>
    cases c with
    | bitvecConst n' b =>
      simp only [LExpr.denoteBitVec] at h
      split at h
      · rename_i hn
        have hn' : n = n' := eq_of_beq hn
        subst hn'; simp only [Option.some.injEq] at h
        exact ⟨m, b, rfl, h⟩
      · simp at h
    | _ => simp [LExpr.denoteBitVec] at h
  | op => simp [LExpr.denoteBitVec] at h
  | bvar => simp [LExpr.denoteBitVec] at h
  | fvar => simp [LExpr.denoteBitVec] at h
  | abs => simp [LExpr.denoteBitVec] at h
  | quant => simp [LExpr.denoteBitVec] at h
  | app => simp [LExpr.denoteBitVec] at h
  | ite => simp [LExpr.denoteBitVec] at h
  | eq => simp [LExpr.denoteBitVec] at h

instance (n : Nat) : InPrim (.bitvec n) (BitVec n) where
  cevalIn := LExpr.denoteBitVec n
  closed := by rfl
  reify_ceval := by
    intro fvarVal vt x h a hx
    obtain ⟨m, b, rfl, rfl⟩ := denoteBitVec_some n x a hx
    rw [Lambda.denote_bitvecConst (T := T) tcInterp opInterp fvarVal vt .nil h]
    simp [reifyAt, LExpr.denoteBitVec, LMonoTy.substTyVars, BitVec.setWidth_eq]

instance (n : Nat) : OutPrim (.bitvec n) (BitVec n) where
  mkOut := fun md w => .const md (.bitvecConst n w)
  closed := by rfl
  gather_eq := by intro vt ceval acc; exact gatherEval_bitvec ceval acc n
  denote_decode := by
    intro fvarVal vt md md' w h
    rw [Lambda.denote_bitvecConst (T := T) tcInterp opInterp fvarVal vt .nil h]
    show w = decodeAt (.bitvec n) (some (.const md' (.bitvecConst n w)))
    unfold decodeAt
    simp

/-- `concreteEval` consistency for any `unaryOp`-built function whose
`LambdaLeanType` decoder/builder agree with the `InPrim`/`OutPrim` bridges.
Stated over `unaryOp` itself so a factory entry unifies with it directly. -/
private theorem unaryOp_func_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV]
    [ip : InPrim inTy InV] [opr : OutPrim outTy OutV]
    (hcin : ip.cevalIn = LambdaLeanType.cevalTy T := by rfl)
    (hmk : opr.mkOut = LambdaLeanType.mkConst T := by rfl)
    {n : T.Identifier} {f : InV → OutV} {guard pre hI hO hp}
    {ceval : ConcreteEval T}
    (hce : (unaryOp n f guard pre hI hO hp).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (unaryOp n f guard pre hI hO hp).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (unaryOp n f guard pre hI hO hp).func ceval := by
  injection hce with hce
  subst hce
  refine unaryOp_consistent (inTy := inTy) (outTy := outTy) _ _ rfl rfl rfl hlook f guard rfl ?_
  intro md opTy x
  rw [hcin, hmk]
  rfl

/-- `concreteEval` consistency for any `binaryOp`-built function whose
`LambdaLeanType` decoder/builder agree with the `InPrim`/`OutPrim` bridges.
Stated over `binaryOp` itself so a factory entry unifies with it directly. -/
private theorem binaryOp_func_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV]
    [ip : InPrim inTy InV] [opr : OutPrim outTy OutV]
    (hcin : ip.cevalIn = LambdaLeanType.cevalTy T := by rfl)
    (hmk : opr.mkOut = LambdaLeanType.mkConst T := by rfl)
    {n : T.Identifier} {g : InV → InV → OutV} {guard pre hI hO hp}
    {ceval : ConcreteEval T}
    (hce : (binaryOp n g guard pre hI hO hp).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (binaryOp n g guard pre hI hO hp).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (binaryOp n g guard pre hI hO hp).func ceval := by
  injection hce with hce
  subst hce
  refine binaryOp_consistent (inTy := inTy) (outTy := outTy) _ _ rfl rfl rfl hlook g guard rfl ?_
  intro md opTy x y
  rw [hcin, hmk]
  rfl

/-- `concreteEval` consistency for any `heteroBinaryOp`-built function whose
`LambdaLeanType` decoders/builder agree with the `InPrim`/`OutPrim` bridges.
Stated over `heteroBinaryOp` itself so a factory entry unifies with it directly. -/
private theorem heteroBinaryOp_func_consistent
    {inTy1 inTy2 outTy : LMonoTy} {InV1 InV2 OutV : Type} [ToString OutV]
    [LambdaLeanType inTy1 InV1] [LambdaLeanType inTy2 InV2] [LambdaLeanType outTy OutV]
    [ip1 : InPrim inTy1 InV1] [ip2 : InPrim inTy2 InV2] [opr : OutPrim outTy OutV]
    (hcin1 : ip1.cevalIn = LambdaLeanType.cevalTy T := by rfl)
    (hcin2 : ip2.cevalIn = LambdaLeanType.cevalTy T := by rfl)
    (hmk : opr.mkOut = LambdaLeanType.mkConst T := by rfl)
    {n : T.Identifier} {g : InV1 → InV2 → OutV} {guard pre hI1 hI2 hO hp}
    {ceval : ConcreteEval T}
    (hce : (heteroBinaryOp n g guard pre hI1 hI2 hO hp).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (heteroBinaryOp n g guard pre hI1 hI2 hO hp).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (heteroBinaryOp n g guard pre hI1 hI2 hO hp).func
      ceval := by
  injection hce with hce
  subst hce
  refine heteroBinaryOp_consistent (inTy1 := inTy1) (inTy2 := inTy2) (outTy := outTy) _ _ rfl rfl rfl
    hlook g guard rfl ?_
  intro md opTy x y
  rw [hcin1, hcin2, hmk]
  rfl

/-- `concreteEval` consistency for any `shortCircuitOp`-built function.
Stated over `shortCircuitOp` itself so a factory entry unifies with it directly. -/
private theorem shortCircuit_func_consistent
    {n : T.Identifier} {absorb decided : Bool}
    {ceval : ConcreteEval T}
    (hce : (shortCircuitOp n absorb decided).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (shortCircuitOp n absorb decided).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (shortCircuitOp n absorb decided).func ceval := by
  injection hce with hce
  subst hce
  exact shortCircuit_consistent _ _ rfl rfl rfl hlook absorb decided rfl
    (by intro md opTy x y; rfl)

/-! ### Consistency of the evaluators on literals

The `Map` and `Sequence` operations (built by `polyLitOp`) evaluate literals. Their arguments
are constants, whose values are given by `constVal`; `AggregateLitEvalSound` states that the
value of the literal an evaluator returns is `axiomOp` applied to the values of its arguments, at
every instantiation of the operation's type, and `litOp_consistent` turns it into
`LFunc.InterpConsistentEval`. -/

/-- Each value of `xs` is the value at its sort of the literal at the same position. -/
def ConstVals : (ss : List LSort) → List LConst → HList (SortDenote tcInterp) ss → Prop
  | [], [], .nil => True
  | s :: ss, c :: cs, .cons x xs => constVal tcInterp s c = some x ∧ ConstVals ss cs xs
  | _, _, _ => False

/-- A typed literal has its denotation as value at the sort of its type. -/
private theorem denote_const_constVal {fv : FreeVarVal T tcInterp} {vt : TyVarVal}
    {m : T.Metadata} {c : LConst} {τ : LMonoTy} (h : LExpr.HasTypeA [] (.const m c) τ) :
    constVal tcInterp (τ.substTyVars vt) c =
      some (LExpr.denote tcInterp opInterp fv vt .nil (.const m c) τ h) := by
  cases h with
  | const hw =>
    rw [denote_const]
    exact constVal_denoteConst (tcInterp := tcInterp) vt hw

/-- Typed literal arguments have their denotations as values. -/
private theorem denoteArgs_constVals {fv : FreeVarVal T tcInterp} {vt : TyVarVal} :
    ∀ (args : List (LExpr T.mono)) (tys : List LMonoTy)
      (h : List.Rel₂ (LExpr.HasTypeA []) args tys) (cs : List LConst),
      LExpr.constArgs? args = some cs →
      ConstVals (tys.map (LMonoTy.substTyVars vt)) cs
        (denoteArgs tcInterp opInterp fv vt .nil args tys h)
  | [], [], _, cs, hc => by
    simp only [LExpr.constArgs?, Option.some.injEq] at hc; subst hc; trivial
  | a :: as, t :: ts, h, cs, hc => by
    cases a with
    | const m c =>
      simp only [LExpr.constArgs?] at hc
      obtain ⟨cs', hcs', rfl⟩ := Option.map_eq_some_iff.mp hc
      exact ⟨denote_const_constVal h.head, denoteArgs_constVals as ts h.tail cs' hcs'⟩
    | _ => simp [LExpr.constArgs?] at hc
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h

/-- The soundness of the literal evaluator `ev` of operation `name`, with input types `inputs`
and output type `output`, against `axiomOp`: at every type instantiation, the value of the
literal it computes from literals is `axiomOp name` applied to their values. -/
def AggregateLitEvalSound (name : String) (inputs : List LMonoTy) (output : LMonoTy)
    (ev : Option LMonoTy → List LConst → Option LConst) : Prop :=
  ∀ (S : Subst) (vt : TyVarVal) (ins : List LSort) (out : LSort)
    (xs : HList (SortDenote tcInterp) ins) (y : SortDenote tcInterp out) (cs : List LConst)
    (r : LConst),
    (inputs.map (LMonoTy.subst S)).map (LMonoTy.substTyVars vt) = ins →
    (output.subst S).substTyVars vt = out →
    ev (some (LMonoTy.mkArrow' (output.subst S) (inputs.map (LMonoTy.subst S)))) cs = some r →
    ConstVals ins cs xs → constVal tcInterp out r = some y →
    y = SortDenote.applyArgs tcInterp (axiomOp name (LSort.mkArrow out ins)) xs

/-- A polymorphic function with a concrete evaluator is interpreted by `axiomOp`. -/
private theorem opInterp_lit {name : String} {func : LFunc T}
    (hlook : Core.Factory.get? name = some func) (hpoly : func.typeArgs.isEmpty = false)
    (s : LSort) : opInterp name s = axiomOp name s := by
  simp only [opInterp, hlook]
  split
  · rfl
  · rw [hpoly]; rfl

/-- `concreteEval` consistency of a `polyLitOp`-built function whose evaluator is sound. -/
private theorem litOp_consistent {n : T.Identifier} {typeArgs : List String}
    {inputs : List (T.Identifier × LMonoTy)} {output : LMonoTy}
    {ev : Option LMonoTy → List LConst → Option LConst} {axs pre h1 h2 h3 h4 h5 h6}
    (hpoly : typeArgs.isEmpty = false)
    (hsound : AggregateLitEvalSound n.name (inputs.map Prod.snd) output ev)
    {ceval : ConcreteEval T}
    (hce : (polyLitOp n typeArgs inputs output ev axs pre h1 h2 h3 h4 h5 h6).func.concreteEval =
      some ceval)
    (hlook : Core.Factory.get? n.name =
      some (polyLitOp n typeArgs inputs output ev axs pre h1 h2 h3 h4 h5 h6).func) :
    LFunc.InterpConsistentEval tcInterp opInterp
      (polyLitOp n typeArgs inputs output ev axs pre h1 h2 h3 h4 h5 h6).func ceval := by
  injection hce with hce
  subst hce
  intro vt fv md S args res
  simp only []
  intro heval h_args h_res
  split at heval
  · obtain ⟨r, hr, hres⟩ := Option.bind_eq_some_iff.mp heval
    obtain ⟨cs, hcs, hev⟩ := Option.bind_eq_some_iff.mp hr
    split at hres
    · simp only [Option.some.injEq] at hres; subst hres
      have hx := denoteArgs_constVals (fv := fv) (vt := vt) args _ h_args cs hcs
      have hy := denote_const_constVal (fv := fv) (vt := vt) h_res
      rw [opInterp_lit
        (name := (polyLitOp n typeArgs inputs output ev axs pre h1 h2 h3 h4 h5 h6).func.name.name)
        hlook hpoly]
      exact hsound S vt _ _ _ _ cs r rfl rfl hev hx hy
    · cases hres
  · cases heval

/-- Literals that have values at no sorts form the empty list. -/
private theorem constVals_nil {cs : List LConst} {xs : HList (SortDenote tcInterp) []}
    (h : ConstVals [] cs xs) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons => cases xs; exact h.elim

/-- Literals that have the values `xs` at the one sort `s` are a single literal, whose value at
    `s` is the one value of `xs`. -/
private theorem constVals_one {s : LSort} {cs : List LConst}
    {xs : HList (SortDenote tcInterp) [s]} (h : ConstVals [s] cs xs) :
    ∃ c x, cs = [c] ∧ xs = .cons x .nil ∧ constVal tcInterp s c = some x := by
  match cs, xs, h with
  | [c], .cons x .nil, ⟨hc, _⟩ => exact ⟨c, x, rfl, rfl, hc⟩
  | [], .cons _ _, h => exact h.elim
  | _ :: _ :: _, .cons _ .nil, h => exact h.2.elim

/-- Literals that have the values `xs` at the two sorts `s₁`, `s₂` are two literals, whose
    values at `s₁` and `s₂` are the two values of `xs`, in order. -/
private theorem constVals_two {s₁ s₂ : LSort} {cs : List LConst}
    {xs : HList (SortDenote tcInterp) [s₁, s₂]} (h : ConstVals [s₁, s₂] cs xs) :
    ∃ c₁ c₂ x₁ x₂, cs = [c₁, c₂] ∧ xs = .cons x₁ (.cons x₂ .nil) ∧
      constVal tcInterp s₁ c₁ = some x₁ ∧ constVal tcInterp s₂ c₂ = some x₂ := by
  match cs, xs, h with
  | [c₁, c₂], .cons x₁ (.cons x₂ .nil), ⟨h₁, h₂, _⟩ => exact ⟨c₁, c₂, x₁, x₂, rfl, rfl, h₁, h₂⟩
  | [], .cons _ _, h => exact h.elim
  | [_], .cons _ (.cons _ _), h => exact h.2.elim
  | _ :: _ :: _ :: _, .cons _ (.cons _ .nil), h => exact h.2.2.elim

/-- Literals that have the values `xs` at the three sorts `s₁`, `s₂`, `s₃` are three literals,
    whose values at `s₁`, `s₂` and `s₃` are the three values of `xs`, in order. -/
private theorem constVals_three {s₁ s₂ s₃ : LSort} {cs : List LConst}
    {xs : HList (SortDenote tcInterp) [s₁, s₂, s₃]} (h : ConstVals [s₁, s₂, s₃] cs xs) :
    ∃ c₁ c₂ c₃ x₁ x₂ x₃, cs = [c₁, c₂, c₃] ∧ xs = .cons x₁ (.cons x₂ (.cons x₃ .nil)) ∧
      constVal tcInterp s₁ c₁ = some x₁ ∧ constVal tcInterp s₂ c₂ = some x₂ ∧
      constVal tcInterp s₃ c₃ = some x₃ := by
  match cs, xs, h with
  | [c₁, c₂, c₃], .cons x₁ (.cons x₂ (.cons x₃ .nil)), ⟨h₁, h₂, h₃, _⟩ =>
    exact ⟨c₁, c₂, c₃, x₁, x₂, x₃, rfl, rfl, h₁, h₂, h₃⟩
  | [], .cons _ _, h => exact h.elim
  | [_], .cons _ (.cons _ _), h => exact h.2.elim
  | [_, _], .cons _ (.cons _ (.cons _ _)), h => exact h.2.2.elim
  | _ :: _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ .nil)), h => exact h.2.2.2.elim

/-- A map literal whose value at sort `Map K V` is `m`: its key and value sorts are `K` and `V`,
and `m` is the map of the values of its default and entries. -/
private theorem constVal_mapConst_inv {K V k v : LSort} {d : LConst}
    {ents : List (LConst × LConst)} {m : SortDenote tcInterp (.tcons "Map" [K, V])}
    (h : constVal tcInterp (.tcons "Map" [K, V]) (.mapConst k v d ⟨ents⟩) = some m) :
    k = K ∧ v = V ∧ ∃ dv kvs, constVal tcInterp v d = some dv ∧
      constValEntries tcInterp k v ents = some kvs ∧ HEq m (SortDenote.mapOf (k := k) dv kvs) := by
  have hs := constVal_sort h
  simp only [LConst.sort, LSort.tcons.injEq, List.cons.injEq, and_true, true_and] at hs
  obtain ⟨rfl, rfl⟩ := hs
  refine ⟨rfl, rfl, ?_⟩
  rw [constVal_mapConst] at h
  split at h
  · rename_i dv kvs hdv hkvs
    exact ⟨dv, kvs, hdv, hkvs, heq_of_eq (Option.some.inj h).symm⟩
  · cases h

/-- A sequence literal whose value at sort `Sequence A` is `sv`: its element sort is `A`, and
`sv` is the list of the values of its elements. -/
private theorem constVal_sequenceConst_inv {A a : LSort} {xs : List LConst}
    {sv : SortDenote tcInterp (.tcons "Sequence" [A])}
    (h : constVal tcInterp (.tcons "Sequence" [A]) (.sequenceConst a ⟨xs⟩) = some sv) :
    a = A ∧ ∃ vals, constValElems tcInterp a xs = some vals ∧ HEq sv vals := by
  have hs := constVal_sort h
  simp only [LConst.sort, LSort.tcons.injEq, List.cons.injEq, and_true, true_and] at hs
  subst hs
  refine ⟨rfl, ?_⟩
  rw [constVal_sequenceConst] at h
  obtain ⟨vals, hv, he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vals, hv, heq_of_eq he.symm⟩

/-- Unfold the instantiated sorts of an operation's inputs and output. -/
macro "lit_sorts" hins:ident hout:ident hev:ident : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, seqTy, mapTy, LMonoTy.subst_tcons,
    LMonoTys.subst_eq_map, LMonoTy.substTyVars, LMonoTy.substTyVars.map,
    LMonoTy.mkArrow', LMonoTy.arrow] at $hins:ident $hout:ident $hev:ident
  subst $hins:ident $hout:ident))

/-- On literal arguments, at every instantiation of its type parameters, the map literal
    `AggregateLitEval.mapConst` builds from a default `d` has as value the model's interpretation of
    `mapConst` (`axiomOp`) at `d`'s value: the constant map. -/
private theorem sound_mapConst :
    AggregateLitEvalSound "mapConst" [.ftvar "v"] (mapTy (.ftvar "k") (.ftvar "v"))
      AggregateLitEval.mapConst := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  obtain ⟨d, dv, rfl, rfl, hd⟩ := constVals_one hx
  simp only [AggregateLitEval.mapConst] at hev
  split at hev
  · rename_i _ ks vs hts
    have hsorts := LMonoTy.toSort?_toMonoTy hts
    simp only [LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.tcons.injEq, List.cons.injEq,
      true_and, and_true] at hsorts
    obtain ⟨-, hks, hvs⟩ := hsorts
    simp only [Option.some.injEq] at hev; subst hev
    have hk := congrArg (LMonoTy.substTyVars vt) hks
    have hv := congrArg (LMonoTy.substTyVars vt) hvs
    rw [LSort.toMonoTy_substTyVars] at hk hv
    generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "k")) = K at *
    generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "v")) = V at *
    subst hk hv
    obtain ⟨-, -, dv', kvs, hd', hkvs, hm⟩ := constVal_mapConst_inv hy
    simp only [constValEntries, Option.some.injEq] at hkvs; subst hkvs
    have hdv : dv' = dv := Option.some.inj (hd'.symm.trans hd)
    subst hdv
    funext z
    rw [eq_of_heq hm]
    show _ = coeS vs vs dv'
    rw [coeS_self]
    rfl
  · cases hev

/-- On literal arguments, at every instantiation of its type parameters, the literal
    `AggregateLitEval.mapSelect` returns for a map literal and a key has as value the model's
    interpretation of `select` (`axiomOp`) at their values: the map's value at the key. -/
private theorem sound_mapSelect :
    AggregateLitEvalSound "select" [mapTy (.ftvar "k") (.ftvar "v"), .ftvar "k"] (.ftvar "v")
      AggregateLitEval.mapSelect := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "k")) = K at *
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "v")) = V at *
  obtain ⟨c₁, key, m, x, rfl, rfl, hm, hkey⟩ := constVals_two hx
  cases c₁ with
  | mapConst k v d ents =>
    obtain ⟨ents⟩ := ents
    simp only [AggregateLitEval.mapSelect] at hev
    split at hev
    · cases hev
    · rename_i hk
      simp only [Option.some.injEq] at hev; subst hev
      obtain ⟨rfl, rfl, dv, kvs, hd, hkvs, hmv⟩ := constVal_mapConst_inv hm
      have hsel := constVal_mapSelect (Bool.eq_false_iff.mpr hk) hd hkvs hkey
      rw [hy, Option.some.injEq] at hsel
      subst hsel
      rw [eq_of_heq hmv]
      show _ = coeS v v (SortDenote.mapOf dv kvs (coeS k k x))
      simp
  | _ => simp [AggregateLitEval.mapSelect] at hev

open Classical in
/-- On literal arguments, at every instantiation of its type parameters, the map literal
    `AggregateLitEval.mapUpdate` builds from a map literal, a key and a value has as value the
    model's interpretation of `update` (`axiomOp`) at their values: the map changed at the key. -/
private theorem sound_mapUpdate :
    AggregateLitEvalSound "update" [mapTy (.ftvar "k") (.ftvar "v"), .ftvar "k", .ftvar "v"]
      (mapTy (.ftvar "k") (.ftvar "v")) AggregateLitEval.mapUpdate := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "k")) = K at *
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "v")) = V at *
  obtain ⟨c₁, key, xc, m, xk, xv, rfl, rfl, hm, hkey, hxv⟩ := constVals_three hx
  cases c₁ with
  | mapConst k v d ents =>
    obtain ⟨ents⟩ := ents
    simp only [AggregateLitEval.mapUpdate] at hev
    split at hev
    · cases hev
    · rename_i hk
      simp only [Option.some.injEq] at hev; subst hev
      obtain ⟨rfl, rfl, dv, kvs, hd, hkvs, hmv⟩ := constVal_mapConst_inv hm
      obtain ⟨kvs', hkvs', hfun⟩ :=
        constValEntries_mapUpdate (Bool.eq_false_iff.mpr hk) hd hkvs hkey hxv
      obtain ⟨-, -, dv', kvs'', hd', hkvs'', hy'⟩ := constVal_mapConst_inv hy
      have hk2 : some kvs'' = some kvs' := hkvs''.symm.trans hkvs'
      have hk3 := Option.some.inj hk2
      have hdv : dv' = dv := Option.some.inj (hd'.symm.trans hd)
      subst hdv hk3
      rw [eq_of_heq hy', eq_of_heq hmv]
      funext z
      show _ = (if coeS k k z = xk then coeS v v xv
        else coeS v v (SortDenote.mapOf dv' kvs (coeS k k z)))
      simp only [coeS_self]
      exact hfun z
  | _ => simp [AggregateLitEval.mapUpdate] at hev

/-- On literal arguments, at every instantiation of its type parameters, the integer
    `AggregateLitEval.seqLength` returns for a sequence literal is the model's interpretation of
    `Sequence.length` (`axiomOp`) at its value: the length of the list. -/
private theorem sound_seqLength :
    AggregateLitEvalSound "Sequence.length" [seqTy (.ftvar "a")] (.tcons "int" [])
      AggregateLitEval.seqLength := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c, sv, rfl, rfl, hs⟩ := constVals_one hx
  cases c with
  | sequenceConst a xs =>
    obtain ⟨xs⟩ := xs
    simp only [AggregateLitEval.seqLength, Option.some.injEq] at hev; subst hev
    obtain ⟨rfl, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
    rw [constVal_intConst] at hy
    have hy := Option.some.inj hy
    subst hy
    obtain ⟨hl, -⟩ := constValElems_iff.mp hvals
    rw [eq_of_heq hsv]
    show (_ : Int) = (vals.length : Int)
    simp [hl]
  | _ => simp [AggregateLitEval.seqLength] at hev

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqEmpty` builds has as value the model's interpretation of `Sequence.empty`
    (`axiomOp`): the empty list. -/
private theorem sound_seqEmpty :
    AggregateLitEvalSound "Sequence.empty" [] (seqTy (.ftvar "a")) AggregateLitEval.seqEmpty := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  cases xs
  obtain rfl := constVals_nil hx
  simp only [AggregateLitEval.seqEmpty] at hev
  split at hev
  · rename_i a hts
    simp only [Option.some.injEq] at hev; subst hev
    have hsorts := LMonoTy.toSort?_toMonoTy hts
    simp only [LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.tcons.injEq, List.cons.injEq,
      true_and, and_true] at hsorts
    have hA := congrArg (LMonoTy.substTyVars vt) hsorts
    rw [LSort.toMonoTy_substTyVars] at hA
    revert y hy
    rw [← hA]
    intro y hy
    obtain ⟨-, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hy
    simp only [constValElems, Option.some.injEq] at hvals; subst hvals
    rw [eq_of_heq hsv]
    rfl
  · cases hev

/-- A sequence literal has as value at its sort the list of the values of its elements. -/
private theorem constVal_seq_of {a : LSort} {arr : Array LConst}
    {vals : List (SortDenote tcInterp a)} (h : constValElems tcInterp a arr.toList = some vals) :
    constVal tcInterp (.tcons "Sequence" [a]) (.sequenceConst a arr) = some vals := by
  cases arr
  rw [constVal_sequenceConst, h]
  rfl

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqAppend` builds from two sequence literals has as value the model's
    interpretation of `Sequence.append` (`axiomOp`) at their values: the concatenation. -/
private theorem sound_seqAppend :
    AggregateLitEvalSound "Sequence.append" [seqTy (.ftvar "a"), seqTy (.ftvar "a")]
      (seqTy (.ftvar "a")) AggregateLitEval.seqAppend := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, tv, rfl, rfl, hs, ht⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    cases c₂ with
    | sequenceConst a' xs₂ =>
      obtain ⟨xs₁⟩ := xs₁
      obtain ⟨xs₂⟩ := xs₂
      simp only [AggregateLitEval.seqAppend, Option.some.injEq] at hev; subst hev
      obtain ⟨ha, v₁, hv₁, hsv⟩ := constVal_sequenceConst_inv hs
      subst A
      obtain ⟨ha', v₂, hv₂, htv⟩ := constVal_sequenceConst_inv ht
      subst a'
      have hy' := constVal_seq_of (arr := (⟨xs₁⟩ : Array LConst) ++ ⟨xs₂⟩)
        (by rw [Array.toList_append]; exact constValElems_append hv₁ hv₂)
      have hyy := Option.some.inj (hy.symm.trans hy'); subst hyy
      rw [eq_of_heq hsv, eq_of_heq htv]
      show _ = ((v₁ ++ v₂.map (coeS a a)).map (coeS a a) : SeqC a)
      simp
    | _ => simp [AggregateLitEval.seqAppend] at hev
  | _ => simp [AggregateLitEval.seqAppend] at hev

/-- On literal arguments, at every instantiation of its type parameters, the literal
    `AggregateLitEval.seqSelect` returns for a sequence literal and an in-bounds index has as value
    the model's interpretation of `Sequence.select` or `Sequence.select!` (`axiomOp`) at their
    values: the element at the index. -/
private theorem sound_seqSelect (name : String) (hname : checkedName name = "Sequence.select") :
    AggregateLitEvalSound name [seqTy (.ftvar "a"), .tcons "int" []] (.ftvar "a")
      AggregateLitEval.seqSelect := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, iv, rfl, rfl, hs, hi⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    cases c₂ with
    | intConst i =>
      obtain ⟨xs₁⟩ := xs₁
      simp only [AggregateLitEval.seqSelect] at hev
      split at hev
      · rename_i hb
        simp only [Option.some.injEq] at hev; subst hev
        obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
        subst A
        rw [constVal_intConst] at hi
        have hi := Option.some.inj hi
        subst hi
        obtain ⟨hl, hv⟩ := constValElems_iff.mp hvals
        have hb2 : i.toNat < xs₁.length := by simpa using hb.2
        have hy' : y = vals[i.toNat]'(hl ▸ hb2) := Option.some.inj (hy.symm.trans (hv _ hb2))
        subst hy'
        rw [show axiomOp name = axiomOpAt (checkedName name) from rfl, hname, eq_of_heq hsv]
        show _ = seqGet a a vals i
        unfold seqGet
        rw [dite_eq_left ⟨hb.1, by omega⟩]
        simp
      · cases hev
    | _ => simp [AggregateLitEval.seqSelect] at hev
  | _ => simp [AggregateLitEval.seqSelect] at hev

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqBuild` builds from a sequence literal and an element has as value the
    model's interpretation of `Sequence.build` (`axiomOp`) at their values: the list with the
    element appended. -/
private theorem sound_seqBuild :
    AggregateLitEvalSound "Sequence.build" [seqTy (.ftvar "a"), .ftvar "a"] (seqTy (.ftvar "a"))
      AggregateLitEval.seqBuild := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, xv, rfl, rfl, hs, hxv⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    obtain ⟨xs₁⟩ := xs₁
    simp only [AggregateLitEval.seqBuild, Option.some.injEq] at hev; subst hev
    obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
    subst A
    have hone : constValElems tcInterp a [c₂] = some [xv] := by simp [constValElems, hxv]
    have hy' := constVal_seq_of (arr := (⟨xs₁⟩ : Array LConst).push c₂)
      (by rw [Array.toList_push]; exact constValElems_append hvals hone)
    have hyy := Option.some.inj (hy.symm.trans hy'); subst hyy
    rw [eq_of_heq hsv]
    show _ = ((vals ++ [coeS a a xv]).map (coeS a a) : SeqC a)
    simp
  | _ => simp [AggregateLitEval.seqBuild] at hev

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqUpdate` builds from a sequence literal, an in-bounds index and an element
    has as value the model's interpretation of `Sequence.update` or `Sequence.update!` (`axiomOp`)
    at their values: the list with the element at the index replaced. -/
private theorem sound_seqUpdate (name : String) (hname : checkedName name = "Sequence.update") :
    AggregateLitEvalSound name [seqTy (.ftvar "a"), .tcons "int" [], .ftvar "a"]
      (seqTy (.ftvar "a")) AggregateLitEval.seqUpdate := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, c₃, sv, iv, xv, rfl, rfl, hs, hi, hxv⟩ := constVals_three hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    cases c₂ with
    | intConst i =>
      obtain ⟨xs₁⟩ := xs₁
      simp only [AggregateLitEval.seqUpdate] at hev
      split at hev
      · rename_i hb
        simp only [Option.some.injEq] at hev; subst hev
        obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
        subst A
        rw [constVal_intConst] at hi
        have hi := Option.some.inj hi
        subst hi
        have hy' := constVal_seq_of (arr := (⟨xs₁⟩ : Array LConst).set i.toNat c₃ hb.2)
          (by rw [Array.toList_set]; exact constValElems_set hvals i.toNat hxv)
        have hyy := Option.some.inj (hy.symm.trans hy'); subst hyy
        rw [show axiomOp name = axiomOpAt (checkedName name) from rfl, hname, eq_of_heq hsv]
        show _ = ((if 0 ≤ i then vals.set i.toNat (coeS a a xv) else vals).map (coeS a a)
          : SeqC a)
        simp [hb.1]
      · cases hev
    | _ => simp [AggregateLitEval.seqUpdate] at hev
  | _ => simp [AggregateLitEval.seqUpdate] at hev

open Classical in
/-- On literal arguments, at every instantiation of its type parameters, the Boolean
    `AggregateLitEval.seqContains` returns for a sequence literal and an element, at an element sort
    without `Map`, is the model's interpretation of `Sequence.contains` (`axiomOp`) at their
    values: whether the list contains the element. -/
private theorem sound_seqContains :
    AggregateLitEvalSound "Sequence.contains" [seqTy (.ftvar "a"), .ftvar "a"] (.tcons "bool" [])
      AggregateLitEval.seqContains := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, xv, rfl, rfl, hs, hxv⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    obtain ⟨xs₁⟩ := xs₁
    simp only [AggregateLitEval.seqContains] at hev
    split at hev
    · cases hev
    · rename_i ha
      simp only [Option.some.injEq] at hev; subst hev
      obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
      subst A
      rw [constVal_boolConst] at hy
      have hy := Option.some.inj hy
      subst hy
      have hiff := constValElems_contains (Bool.eq_false_iff.mpr ha) hvals hxv
      rw [eq_of_heq hsv]
      show _ = decide (∃ i : Int, 0 ≤ i ∧ i < (vals.length : Int) ∧ seqGet a a vals i = xv)
      have hac : ((⟨xs₁⟩ : Array LConst).contains c₂ = true) ↔ (xs₁.contains c₂ = true) := by
        simp
      apply Bool.eq_iff_iff.mpr
      rw [hac, hiff, decide_eq_true_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, by omega, by omega, ?_⟩
        unfold seqGet
        rw [dite_eq_left ⟨by omega, by simpa using hi⟩]
        simp
      · rintro ⟨i, h0, hi, heq⟩
        refine ⟨i.toNat, by omega, ?_⟩
        unfold seqGet at heq
        rw [dite_eq_left ⟨h0, by omega⟩] at heq
        simpa using heq
  | _ => simp [AggregateLitEval.seqContains] at hev

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqTake` builds from a sequence literal and a count between `0` and its length
    has as value the model's interpretation of `Sequence.take` or `Sequence.take!` (`axiomOp`) at
    their values: the list's first elements. -/
private theorem sound_seqTake (name : String) (hname : checkedName name = "Sequence.take") :
    AggregateLitEvalSound name [seqTy (.ftvar "a"), .tcons "int" []] (seqTy (.ftvar "a"))
      AggregateLitEval.seqTake := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, nv, rfl, rfl, hs, hn⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    cases c₂ with
    | intConst n =>
      obtain ⟨xs₁⟩ := xs₁
      simp only [AggregateLitEval.seqTake] at hev
      split at hev
      · simp only [Option.some.injEq] at hev; subst hev
        obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
        subst A
        rw [constVal_intConst] at hn
        have hn := Option.some.inj hn
        subst hn
        have hy' := constVal_seq_of (arr := (⟨xs₁⟩ : Array LConst).extract 0 n.toNat)
          (by
            rw [Array.toList_extract, List.extract_eq_take_drop]
            simpa using constValElems_take hvals n.toNat)
        have hyy := Option.some.inj (hy.symm.trans hy'); subst hyy
        rw [show axiomOp name = axiomOpAt (checkedName name) from rfl, hname, eq_of_heq hsv]
        show _ = ((vals.take n.toNat).map (coeS a a) : SeqC a)
        simp
      · cases hev
    | _ => simp [AggregateLitEval.seqTake] at hev
  | _ => simp [AggregateLitEval.seqTake] at hev

/-- On literal arguments, at every instantiation of its type parameters, the sequence literal
    `AggregateLitEval.seqDrop` builds from a sequence literal and a count between `0` and its length
    has as value the model's interpretation of `Sequence.drop` or `Sequence.drop!` (`axiomOp`) at
    their values: the list without its first elements. -/
private theorem sound_seqDrop (name : String) (hname : checkedName name = "Sequence.drop") :
    AggregateLitEvalSound name [seqTy (.ftvar "a"), .tcons "int" []] (seqTy (.ftvar "a"))
      AggregateLitEval.seqDrop := by
  intro S vt ins out xs y cs r hins hout hev hx hy
  lit_sorts hins hout hev
  generalize LMonoTy.substTyVars vt (LMonoTy.subst S (.ftvar "a")) = A at *
  obtain ⟨c₁, c₂, sv, nv, rfl, rfl, hs, hn⟩ := constVals_two hx
  cases c₁ with
  | sequenceConst a xs₁ =>
    cases c₂ with
    | intConst n =>
      obtain ⟨xs₁⟩ := xs₁
      simp only [AggregateLitEval.seqDrop] at hev
      split at hev
      · rename_i hb
        simp only [Option.some.injEq] at hev; subst hev
        obtain ⟨ha, vals, hvals, hsv⟩ := constVal_sequenceConst_inv hs
        subst A
        rw [constVal_intConst] at hn
        have hn := Option.some.inj hn
        subst hn
        have hy' := constVal_seq_of
          (arr := (⟨xs₁⟩ : Array LConst).extract n.toNat (⟨xs₁⟩ : Array LConst).size)
          (by
            rw [Array.toList_extract, List.extract_eq_take_drop,
              List.take_of_length_le (by simp)]
            exact constValElems_drop hvals n.toNat)
        have hy'' : y = vals.drop n.toNat := Option.some.inj (hy.symm.trans hy')
        subst hy''
        rw [show axiomOp name = axiomOpAt (checkedName name) from rfl, hname, eq_of_heq hsv]
        show _ = ((if 0 ≤ n then vals.drop n.toNat
          else List.replicate (-n).toNat (default : SortDenote tcInterp a) ++ vals).map
            (coeS a a) : SeqC a)
        simp [hb.1]
      · cases hev
    | _ => simp [AggregateLitEval.seqDrop] at hev
  | _ => simp [AggregateLitEval.seqDrop] at hev

/-- For every `Core.Factory` function with a concrete evaluator, `opInterp` agrees
    with that evaluator. -/
private theorem eval_consistent :
    ∀ (f : String), (hf : f ∈ Core.Factory) → ∀ ceval, (Core.Factory[f]).concreteEval = some ceval →
      LFunc.InterpConsistentEval tcInterp opInterp (Core.Factory[f]) ceval := by
  -- Each entry is either evaluator-free or built by `unaryOp`/`binaryOp`/`heteroBinaryOp`.
  have hall : ∀ wf ∈ Core.WFFactoryArray.toList, ∀ ceval,
      wf.func.concreteEval = some ceval →
      Core.Factory.get? wf.func.name.name = some wf.func →
      LFunc.InterpConsistentEval tcInterp opInterp wf.func ceval := by
    unfold Core.WFFactoryArray
    simp only [Array.toList_appendList, List.forall_mem_append]
    repeat' apply And.intro
    all_goals
      repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
      exact List.forall_mem_nil _
    all_goals
      intro ceval hce hlook
      first
      | (injection hce; done)
      | exact binaryOp_func_consistent (hce := hce) (hlook := hlook)
      | exact heteroBinaryOp_func_consistent (hce := hce) (hlook := hlook)
      | exact unaryOp_func_consistent (hce := hce) (hlook := hlook)
      | exact shortCircuit_func_consistent (hce := hce) (hlook := hlook)
      | exact litOp_consistent rfl sound_mapConst hce hlook
      | exact litOp_consistent rfl sound_mapSelect hce hlook
      | exact litOp_consistent rfl sound_mapUpdate hce hlook
      | exact litOp_consistent rfl sound_seqLength hce hlook
      | exact litOp_consistent rfl sound_seqEmpty hce hlook
      | exact litOp_consistent rfl sound_seqAppend hce hlook
      | exact litOp_consistent rfl (sound_seqSelect _ rfl) hce hlook
      | exact litOp_consistent rfl sound_seqBuild hce hlook
      | exact litOp_consistent rfl (sound_seqUpdate _ rfl) hce hlook
      | exact litOp_consistent rfl sound_seqContains hce hlook
      | exact litOp_consistent rfl (sound_seqTake _ rfl) hce hlook
      | exact litOp_consistent rfl (sound_seqDrop _ rfl) hce hlook
  intro f hf ceval hce
  have hmem : Core.Factory[f] ∈ Core.WFFactoryArray.map (·.func) :=
    Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) (get_mem f hf)
  generalize Core.Factory[f] = fn at hmem hce ⊢
  have hlook : Core.Factory.get? fn.name.name = some fn :=
    Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup
  obtain ⟨wf, hwf, rfl⟩ := Array.mem_map.mp hmem
  exact hall wf (Array.mem_def.mp hwf) ceval hce hlook

/-- `ConstrInterpConsistent`: vacuous, since no factory function is a
constructor. -/
private theorem constr_consistent : ConstrInterpConsistent tcInterp opInterp Core.Factory := by
  have hnc : ∀ f ∈ Core.Factory.toArray, ¬ f.isConstr = true := by
    intro f hf hc
    rw [all_not_constr f hf] at hc
    cases hc
  constructor
  · intro f1 _ hf1 _ hc1 _ _ _; exact absurd hc1 (hnc f1 hf1)
  · intro f hf hc; exact absurd hc (hnc f hf)
  · intro P _ s v hs
    obtain ⟨f, hf, hc, -⟩ := hs
    exact absurd hc (hnc f hf)

/-! ### The axioms of `Core.Factory` hold in the model

The axioms are checked one built-in function at a time. For each axiom, `ax_close`
peels its universal quantifiers, computes its value with `denotes`, rewrites the
interpretation of each operator it applies (the `opInterp_…` lemmas), and closes the
resulting statement about Lean values. -/

/-- Prove that a built-in function is listed in `Core.WFFactoryArray`. -/
macro "wf_mem" : tactic => `(tactic| (
  simp only [Core.WFFactoryArray, Array.toList_appendList, List.mem_append, List.mem_cons,
    true_or, or_true]))

/-- A built-in function is found in `Core.Factory` under its name. -/
private theorem get?_wf {wf : WFLFunc CoreLParams} (h : wf ∈ Core.WFFactoryArray.toList) :
    Core.Factory.get? wf.func.name.name = some wf.func := by
  have hmem : wf.func ∈ Core.WFFactoryArray.map (·.func) :=
    Array.mem_map.mpr ⟨wf, Array.mem_def.mpr h, rfl⟩
  have hCoreEq : Core.Factory = Lambda.Factory.ofArray (Core.WFFactoryArray.map (·.func)) := rfl
  rw [hCoreEq]
  exact Lambda.Factory.get?_ofArray_of_mem hmem Core.WFFactoryArray_func_name_nodup

/-- A built-in function without a concrete evaluator is interpreted by `axiomOp`. -/
private theorem opInterp_axiom {wf : WFLFunc CoreLParams} (h : wf ∈ Core.WFFactoryArray.toList)
    (hce : wf.func.concreteEval = none) (s : LSort) :
    opInterp wf.func.name.name s = axiomOp wf.func.name.name s := by
  simp only [opInterp, get?_wf h, hce]

/-- A polymorphic built-in function is interpreted by `axiomOp`. -/
private theorem opInterp_poly {wf : WFLFunc CoreLParams} (h : wf ∈ Core.WFFactoryArray.toList)
    (hpoly : wf.func.typeArgs.isEmpty = false) (s : LSort) :
    opInterp wf.func.name.name s = axiomOp wf.func.name.name s :=
  opInterp_lit (get?_wf h) hpoly s

/-! #### Interpretations of the operators the axioms use -/

section OpLemmas
/- `wf_mem` rewrites a membership in the whole factory array, a disjunction of about 200
equations, which needs more than the default recursion depth. -/
set_option maxRecDepth 2000

variable (k v k' v' k1 v1 k2 v2 a a' a'' b : LSort)

/-- The arrow sort. -/
local macro "arr" x:term:max y:term:max : term => `(LSort.tcons "arrow" [$x, $y])

/-- The model interprets `Int.Ge` as the Lean comparison `x ≥ y` on integers. -/
private theorem opInterp_intGe :
    opInterp "Int.Ge" (arr .int (arr .int .bool)) = fun (x y : Int) => decide (x ≥ y) := by
  have hl : Core.Factory.get? "Int.Ge" = some (intGeFunc (T := CoreLParams)).func :=
    get?_wf (wf := intGeFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; rfl

/-- The model interprets `Int.Lt` as the Lean comparison `x < y` on integers. -/
private theorem opInterp_intLt :
    opInterp "Int.Lt" (arr .int (arr .int .bool)) = fun (x y : Int) => decide (x < y) := by
  have hl : Core.Factory.get? "Int.Lt" = some (intLtFunc (T := CoreLParams)).func :=
    get?_wf (wf := intLtFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; rfl

/-- The model interprets `Int.Le` as the Lean comparison `x ≤ y` on integers. -/
private theorem opInterp_intLe :
    opInterp "Int.Le" (arr .int (arr .int .bool)) = fun (x y : Int) => decide (x ≤ y) := by
  have hl : Core.Factory.get? "Int.Le" = some (intLeFunc (T := CoreLParams)).func :=
    get?_wf (wf := intLeFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; rfl

/-- The model interprets `Int.Add` as integer addition. -/
private theorem opInterp_intAdd :
    opInterp "Int.Add" (arr .int (arr .int .int)) = fun (x y : Int) => x + y := by
  have hl : Core.Factory.get? "Int.Add" = some (intAddFunc (T := CoreLParams)).func :=
    get?_wf (wf := intAddFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; rfl

/-- The model interprets `Int.Sub` as integer subtraction. -/
private theorem opInterp_intSub :
    opInterp "Int.Sub" (arr .int (arr .int .int)) = fun (x y : Int) => x - y := by
  have hl : Core.Factory.get? "Int.Sub" = some (intSubFunc (T := CoreLParams)).func :=
    get?_wf (wf := intSubFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; rfl

/-- The model interprets `Bool.And` as Boolean conjunction. -/
private theorem opInterp_boolAnd :
    opInterp "Bool.And" (arr .bool (arr .bool .bool)) = fun (x y : Bool) => x && y := by
  have hl : Core.Factory.get? "Bool.And" = some (boolAndFunc (T := CoreLParams)).func :=
    get?_wf (wf := boolAndFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; cases x <;> cases y <;> rfl

/-- The model interprets `Bool.Or` as Boolean disjunction. -/
private theorem opInterp_boolOr :
    opInterp "Bool.Or" (arr .bool (arr .bool .bool)) = fun (x y : Bool) => x || y := by
  have hl : Core.Factory.get? "Bool.Or" = some (boolOrFunc (T := CoreLParams)).func :=
    get?_wf (wf := boolOrFunc) (by wf_mem)
  funext x y; simp only [opInterp, hl]; cases x <;> cases y <;> rfl

/-- The model interprets `Bool.Not` as Boolean negation. -/
private theorem opInterp_boolNot :
    opInterp "Bool.Not" (arr .bool .bool) = fun (x : Bool) => !x := by
  have hl : Core.Factory.get? "Bool.Not" = some (boolNotFunc (T := CoreLParams)).func :=
    get?_wf (wf := boolNotFunc) (by wf_mem)
  funext x; simp only [opInterp, hl]; cases x <;> rfl

/-- The model interprets `mapConst` as the constant function returning its argument. -/
private theorem opInterp_mapConst (d : SortDenote tcInterp v) (z : SortDenote tcInterp k) :
    opInterp "mapConst" (arr v (.tcons "Map" [k, v'])) d z = coeS v v' d := by
  rw [show opInterp "mapConst" (arr v (.tcons "Map" [k, v'])) = axiomOp "mapConst" _ from
    opInterp_poly (wf := mapConstFunc) (by wf_mem) rfl _]; rfl

/-- The model interprets `select` as applying the map, a function, to the key. -/
private theorem opInterp_select (mm : SortDenote tcInterp (.tcons "Map" [k, v]))
    (x : SortDenote tcInterp k') :
    opInterp "select" (arr (.tcons "Map" [k, v]) (arr k' v')) mm x =
      coeS v v' ((mm : MapC k v) (coeS k' k x)) := by
  rw [show opInterp "select" (arr (.tcons "Map" [k, v]) (arr k' v')) = axiomOp "select" _ from
    opInterp_poly (wf := mapSelectFunc) (by wf_mem) rfl _]; rfl

open Classical in
/-- The model interprets `update` as the function that returns the new value at the updated key
and the old map's value elsewhere. -/
private theorem opInterp_update (mm : SortDenote tcInterp (.tcons "Map" [k, v]))
    (x : SortDenote tcInterp k1)
    (y : SortDenote tcInterp v1) (z : SortDenote tcInterp k2) :
    opInterp "update" (arr (.tcons "Map" [k, v]) (arr k1 (arr v1 (.tcons "Map" [k2, v2]))))
        mm x y z =
      if coeS k2 k1 z = x then coeS v1 v2 y else coeS v v2 ((mm : MapC k v) (coeS k2 k z))
      := by
  rw [show opInterp "update" (arr (.tcons "Map" [k, v]) (arr k1 (arr v1 (.tcons "Map" [k2, v2]))))
      = axiomOp "update" _ from opInterp_poly (wf := mapUpdateFunc) (by wf_mem) rfl _]; rfl


/-- The model interprets `Set.empty` as the predicate that holds of no element. -/
private theorem opInterp_setEmpty (y : Carrier a) :
    opInterp "Set.empty" (.tcons "Set" [a]) y = false := by
  rw [show opInterp "Set.empty" (.tcons "Set" [a]) = axiomOp "Set.empty" _ from
    opInterp_axiom (wf := setEmptyFunc) (by wf_mem) rfl _]; rfl

/-- The model interprets `Set.contains` as applying the set's membership predicate to the
element. -/
private theorem opInterp_setContains (st : SortDenote tcInterp (.tcons "Set" [a]))
    (x : SortDenote tcInterp a') :
    opInterp "Set.contains" (arr (.tcons "Set" [a]) (arr a' (.tcons "bool" []))) st x =
      (st : SetC a) (coe a' a (toC x)) := by
  rw [show opInterp "Set.contains" (arr (.tcons "Set" [a]) (arr a' (.tcons "bool" [])))
      = axiomOp "Set.contains" _ from opInterp_axiom (wf := setContainsFunc) (by wf_mem) rfl _]
  rfl

open Classical in
/-- The model interprets `Set.insert` as the predicate that holds of the inserted element and of
every member of the set. -/
private theorem opInterp_setInsert (st : SortDenote tcInterp (.tcons "Set" [a]))
    (x : SortDenote tcInterp a') (y : Carrier a'') :
    opInterp "Set.insert" (arr (.tcons "Set" [a]) (arr a' (.tcons "Set" [a'']))) st x y =
      (decide (coe a'' a' y = toC x) || (st : SetC a) (coe a'' a y)) := by
  rw [show opInterp "Set.insert" (arr (.tcons "Set" [a]) (arr a' (.tcons "Set" [a''])))
      = axiomOp "Set.insert" _ from opInterp_axiom (wf := setInsertFunc) (by wf_mem) rfl _]
  rfl

open Classical in
/-- The model interprets `Set.remove` as the predicate that holds of every member of the set
except the removed element. -/
private theorem opInterp_setRemove (st : SortDenote tcInterp (.tcons "Set" [a]))
    (x : SortDenote tcInterp a') (y : Carrier a'') :
    opInterp "Set.remove" (arr (.tcons "Set" [a]) (arr a' (.tcons "Set" [a'']))) st x y =
      (!decide (coe a'' a' y = toC x) && (st : SetC a) (coe a'' a y)) := by
  rw [show opInterp "Set.remove" (arr (.tcons "Set" [a]) (arr a' (.tcons "Set" [a''])))
      = axiomOp "Set.remove" _ from opInterp_axiom (wf := setRemoveFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Set.union` as the pointwise disjunction of the two sets' membership
predicates. -/
private theorem opInterp_setUnion (st : SortDenote tcInterp (.tcons "Set" [a]))
    (t : SortDenote tcInterp (.tcons "Set" [a'])) (y : Carrier a'') :
    opInterp "Set.union" (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
        st t y = ((st : SetC a) (coe a'' a y) || (t : SetC a') (coe a'' a' y)) := by
  rw [show opInterp "Set.union"
      (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
      = axiomOp "Set.union" _ from opInterp_axiom (wf := setUnionFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Set.intersect` as the pointwise conjunction of the two sets' membership
predicates. -/
private theorem opInterp_setIntersect (st : SortDenote tcInterp (.tcons "Set" [a]))
    (t : SortDenote tcInterp (.tcons "Set" [a'])) (y : Carrier a'') :
    opInterp "Set.intersect"
        (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
        st t y = ((st : SetC a) (coe a'' a y) && (t : SetC a') (coe a'' a' y)) := by
  rw [show opInterp "Set.intersect"
      (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
      = axiomOp "Set.intersect" _ from opInterp_axiom (wf := setIntersectFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Set.difference` as the predicate that holds of members of the first set
that are not members of the second. -/
private theorem opInterp_setDifference (st : SortDenote tcInterp (.tcons "Set" [a]))
    (t : SortDenote tcInterp (.tcons "Set" [a'])) (y : Carrier a'') :
    opInterp "Set.difference"
        (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
        st t y = ((st : SetC a) (coe a'' a y) && !(t : SetC a') (coe a'' a' y)) := by
  rw [show opInterp "Set.difference"
      (arr (.tcons "Set" [a]) (arr (.tcons "Set" [a']) (.tcons "Set" [a''])))
      = axiomOp "Set.difference" _ from
        opInterp_axiom (wf := setDifferenceFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.length` as the length of the list. -/
private theorem opInterp_seqLength (s : SortDenote tcInterp (.tcons "Sequence" [a])) :
    opInterp "Sequence.length" (arr (.tcons "Sequence" [a]) (.tcons "int" [])) s =
      ((s : SeqC a).length : Int) := by
  rw [show opInterp "Sequence.length" (arr (.tcons "Sequence" [a]) (.tcons "int" []))
      = axiomOp "Sequence.length" _ from opInterp_poly (wf := seqLengthFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.empty` as the empty list. -/
private theorem opInterp_seqEmpty :
    opInterp "Sequence.empty" (.tcons "Sequence" [a]) = ([] : SeqC a) := by
  rw [show opInterp "Sequence.empty" (.tcons "Sequence" [a]) = axiomOp "Sequence.empty" _ from
    opInterp_poly (wf := seqEmptyFunc) (by wf_mem) rfl _]; rfl

/-- The model interprets `Sequence.append` as list concatenation. -/
private theorem opInterp_seqAppend (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (t : SortDenote tcInterp (.tcons "Sequence" [a'])) :
    opInterp "Sequence.append"
        (arr (.tcons "Sequence" [a]) (arr (.tcons "Sequence" [a']) (.tcons "Sequence" [a''])))
        s t = (List.map (coeS a a'') (List.append (s : SeqC a) (List.map (coeS a' a) (t : SeqC a')))
          : SeqC a'') := by
  rw [show opInterp "Sequence.append"
      (arr (.tcons "Sequence" [a]) (arr (.tcons "Sequence" [a']) (.tcons "Sequence" [a''])))
      = axiomOp "Sequence.append" _ from opInterp_poly (wf := seqAppendFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.select` as list indexing, with a default value out of range. -/
private theorem opInterp_seqSelect (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (i : SortDenote tcInterp (.tcons "int" [])) :
    opInterp "Sequence.select" (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) b)) s i =
      seqGet a b s i := by
  rw [show opInterp "Sequence.select" (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) b))
      = axiomOp "Sequence.select" _ from opInterp_poly (wf := seqSelectFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.build` as appending one element at the end of the list. -/
private theorem opInterp_seqBuild (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (x : SortDenote tcInterp a') :
    opInterp "Sequence.build" (arr (.tcons "Sequence" [a]) (arr a' (.tcons "Sequence" [a''])))
        s x = (List.map (coeS a a'') (List.append (s : SeqC a) [coeS a' a x]) : SeqC a'') := by
  rw [show opInterp "Sequence.build"
      (arr (.tcons "Sequence" [a]) (arr a' (.tcons "Sequence" [a''])))
      = axiomOp "Sequence.build" _ from opInterp_poly (wf := seqBuildFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.update` as replacing the element at a non-negative index (a
negative index leaves the list unchanged, and so does an index past the end). -/
private theorem opInterp_seqUpdate (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (i : SortDenote tcInterp (.tcons "int" [])) (x : SortDenote tcInterp a') :
    opInterp "Sequence.update"
        (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (arr a' (.tcons "Sequence" [a'']))))
        s i x =
      ((if 0 ≤ @id Int i then (s : SeqC a).set (@id Int i).toNat (coeS a' a x)
        else (s : SeqC a)).map
        (coeS a a'') : SeqC a'') := by
  rw [show opInterp "Sequence.update"
      (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (arr a' (.tcons "Sequence" [a'']))))
      = axiomOp "Sequence.update" _ from opInterp_poly (wf := seqUpdateFunc) (by wf_mem) rfl _]
  rfl

open Classical in
/-- The model interprets `Sequence.contains` as whether some in-range index holds an element equal
to the given one. -/
private theorem opInterp_seqContains (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (x : SortDenote tcInterp a') :
    opInterp "Sequence.contains" (arr (.tcons "Sequence" [a]) (arr a' (.tcons "bool" []))) s x =
      decide (∃ i : Int, 0 ≤ i ∧ i < ((s : SeqC a).length : Int) ∧ seqGet a a' s i = x) := by
  rw [show opInterp "Sequence.contains"
      (arr (.tcons "Sequence" [a]) (arr a' (.tcons "bool" [])))
      = axiomOp "Sequence.contains" _ from
        opInterp_poly (wf := seqContainsFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.take` as the first `n` elements of the list (none for a
negative `n`). -/
private theorem opInterp_seqTake (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (n : SortDenote tcInterp (.tcons "int" [])) :
    opInterp "Sequence.take"
        (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (.tcons "Sequence" [a']))) s n =
      (((s : SeqC a).take (@id Int n).toNat).map (coeS a a') : SeqC a') := by
  rw [show opInterp "Sequence.take"
      (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (.tcons "Sequence" [a'])))
      = axiomOp "Sequence.take" _ from opInterp_poly (wf := seqTakeFunc) (by wf_mem) rfl _]
  rfl

/-- The model interprets `Sequence.drop` as the list without its first `n` elements; for a
negative `n`, the list is padded at the front with `-n` default values. -/
private theorem opInterp_seqDrop (s : SortDenote tcInterp (.tcons "Sequence" [a]))
    (n : SortDenote tcInterp (.tcons "int" [])) :
    opInterp "Sequence.drop"
        (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (.tcons "Sequence" [a']))) s n =
      ((if 0 ≤ @id Int n then (s : SeqC a).drop (@id Int n).toNat
        else List.replicate (-(@id Int n)).toNat (default : SortDenote tcInterp a) ++
          @id (SeqC a) s).map (coeS a a')
        : SeqC a') := by
  rw [show opInterp "Sequence.drop"
      (arr (.tcons "Sequence" [a]) (arr (.tcons "int" []) (.tcons "Sequence" [a'])))
      = axiomOp "Sequence.drop" _ from opInterp_poly (wf := seqDropFunc) (by wf_mem) rfl _]
  rfl

/-- The unchecked sequence operations are interpreted as their checked counterparts. -/
private theorem opInterp_seqSelectBang :
    opInterp "Sequence.select!" = opInterp "Sequence.select" := by
  have h1 : Core.Factory.get? "Sequence.select!" = some seqSelectUnsafeFunc.func :=
    get?_wf (wf := seqSelectUnsafeFunc) (by wf_mem)
  have h2 : Core.Factory.get? "Sequence.select" = some seqSelectFunc.func :=
    get?_wf (wf := seqSelectFunc) (by wf_mem)
  funext s; simp only [opInterp, h1, h2]; rfl

/-- The model interprets `Sequence.update!` as `Sequence.update`. -/
private theorem opInterp_seqUpdateBang :
    opInterp "Sequence.update!" = opInterp "Sequence.update" := by
  have h1 : Core.Factory.get? "Sequence.update!" = some seqUpdateUnsafeFunc.func :=
    get?_wf (wf := seqUpdateUnsafeFunc) (by wf_mem)
  have h2 : Core.Factory.get? "Sequence.update" = some seqUpdateFunc.func :=
    get?_wf (wf := seqUpdateFunc) (by wf_mem)
  funext s; simp only [opInterp, h1, h2]; rfl

/-- The model interprets `Sequence.take!` as `Sequence.take`. -/
private theorem opInterp_seqTakeBang : opInterp "Sequence.take!" = opInterp "Sequence.take" := by
  have h1 : Core.Factory.get? "Sequence.take!" = some seqTakeUnsafeFunc.func :=
    get?_wf (wf := seqTakeUnsafeFunc) (by wf_mem)
  have h2 : Core.Factory.get? "Sequence.take" = some seqTakeFunc.func :=
    get?_wf (wf := seqTakeFunc) (by wf_mem)
  funext s; simp only [opInterp, h1, h2]; rfl

/-- The model interprets `Sequence.drop!` as `Sequence.drop`. -/
private theorem opInterp_seqDropBang : opInterp "Sequence.drop!" = opInterp "Sequence.drop" := by
  have h1 : Core.Factory.get? "Sequence.drop!" = some seqDropUnsafeFunc.func :=
    get?_wf (wf := seqDropUnsafeFunc) (by wf_mem)
  have h2 : Core.Factory.get? "Sequence.drop" = some seqDropFunc.func :=
    get?_wf (wf := seqDropFunc) (by wf_mem)
  funext s; simp only [opInterp, h1, h2]; rfl

/-- The model interprets a real operation, built by `binaryFuncUneval` or `unaryFuncUneval`,
by `axiomOp`, whose case for it is the given operation of `Strata.Util.Real`. -/
local macro "real_op" wf:ident : term =>
  `((opInterp_axiom (wf := $wf) (by wf_mem) rfl _).trans rfl)

/-- The model interprets `Real.Add` as addition on `Real`. -/
private theorem opInterp_realAdd :
    opInterp "Real.Add" (arr .real (arr .real .real)) = fun (x y : Strata.Util.Real) => x + y :=
  real_op realAddFunc

/-- The model interprets `Real.Sub` as subtraction on `Real`. -/
private theorem opInterp_realSub :
    opInterp "Real.Sub" (arr .real (arr .real .real)) = fun (x y : Strata.Util.Real) => x - y :=
  real_op realSubFunc

/-- The model interprets `Real.Mul` as multiplication on `Real`. -/
private theorem opInterp_realMul :
    opInterp "Real.Mul" (arr .real (arr .real .real)) = fun (x y : Strata.Util.Real) => x * y :=
  real_op realMulFunc

/-- The model interprets `Real.Div` as division on `Real`, which is `0` at a zero divisor. -/
private theorem opInterp_realDiv :
    opInterp "Real.Div" (arr .real (arr .real .real)) = fun (x y : Strata.Util.Real) => x / y :=
  real_op realDivFunc

/-- The model interprets `Real.Neg` as negation on `Real`. -/
private theorem opInterp_realNeg :
    opInterp "Real.Neg" (arr .real .real) = fun (x : Strata.Util.Real) => -x :=
  real_op realNegFunc

open Classical in
/-- The model interprets `Real.Lt` as the order `x < y` on `Real`. -/
private theorem opInterp_realLt :
    opInterp "Real.Lt" (arr .real (arr .real .bool)) = fun (x y : Strata.Util.Real) => decide (x < y) :=
  real_op realLtFunc

open Classical in
/-- The model interprets `Real.Le` as the order `x ≤ y` on `Real`. -/
private theorem opInterp_realLe :
    opInterp "Real.Le" (arr .real (arr .real .bool)) = fun (x y : Strata.Util.Real) => decide (x ≤ y) :=
  real_op realLeFunc

open Classical in
/-- The model interprets `Real.Gt` as the order `x > y` on `Real`. -/
private theorem opInterp_realGt :
    opInterp "Real.Gt" (arr .real (arr .real .bool)) = fun (x y : Strata.Util.Real) => decide (x > y) :=
  real_op realGtFunc

open Classical in
/-- The model interprets `Real.Ge` as the order `x ≥ y` on `Real`. -/
private theorem opInterp_realGe :
    opInterp "Real.Ge" (arr .real (arr .real .bool)) = fun (x y : Strata.Util.Real) => decide (x ≥ y) :=
  real_op realGeFunc

end OpLemmas


/-! #### Indexing into sequences -/


/-- Reading index `j < n` of the first `n` elements reads index `j` of the sequence. -/
private theorem seqGet_take {a b : LSort} (s : List (SortDenote tcInterp a)) (n j : Int)
    (h0 : 0 ≤ j) (hj : j < n) :
    seqGet a b (s.take n.toNat) j = seqGet a b s j := by
  unfold seqGet
  by_cases hs : j.toNat < s.length
  · rw [dite_eq_left ⟨h0, by simp; omega⟩, dite_eq_left ⟨h0, hs⟩]
    simp [List.getElem_take]
  · rw [dite_eq_right (by simp; omega), dite_eq_right (by omega)]

/-- Reading an index of `s ++ t` inside `s` reads it in `s`. -/
private theorem seqGet_append_left {a b : LSort} (s t : List (SortDenote tcInterp a)) (i : Int)
    (h0 : 0 ≤ i) (hi : i < s.length) : seqGet a b (s ++ t) i = seqGet a b s i := by
  unfold seqGet
  rw [dite_eq_left ⟨h0, by simp; omega⟩, dite_eq_left ⟨h0, by omega⟩]
  simp [List.getElem_append_left (show i.toNat < s.length by omega)]

/-- Reading an index of `s ++ t` past `s` reads `t` at the index shifted by the length of `s`. -/
private theorem seqGet_append_right {a b : LSort} (s t : List (SortDenote tcInterp a)) (i : Int)
    (h0 : s.length ≤ i) (hi : i < s.length + t.length) :
    seqGet a b (s ++ t) i = seqGet a b t (i - s.length) := by
  unfold seqGet
  rw [dite_eq_left ⟨by omega, by simp; omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  rw [List.getElem_append_right (show s.length ≤ i.toNat by omega)]
  congr 3; omega

/-- Reading index `length s` of `s ++ [x]` reads `x`. -/
private theorem seqGet_append_last {a b : LSort} (s : List (SortDenote tcInterp a))
    (x : SortDenote tcInterp a) :
    seqGet a b (s ++ [x]) s.length = coeS a b x := by
  unfold seqGet
  rw [dite_eq_left ⟨by omega, by simp⟩]
  simp

/-- Reading an in-range index just set reads the new element. -/
private theorem seqGet_set_same {a b : LSort} (s : List (SortDenote tcInterp a)) (i : Int)
    (x : SortDenote tcInterp a)
    (h0 : 0 ≤ i) (hi : i < s.length) : seqGet a b (s.set i.toNat x) i = coeS a b x := by
  unfold seqGet
  rw [dite_eq_left ⟨h0, by simp; omega⟩]
  simp

/-- Setting one index leaves every other non-negative index unchanged. -/
private theorem seqGet_set_ne {a b : LSort} (s : List (SortDenote tcInterp a)) (i j : Int)
    (x : SortDenote tcInterp a)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : j ≠ i) :
    seqGet a b (s.set i.toNat x) j = seqGet a b s j := by
  unfold seqGet
  by_cases hs : j.toNat < s.length
  · rw [dite_eq_left ⟨hj, by simp; omega⟩, dite_eq_left ⟨hj, hs⟩]
    rw [List.getElem_set_ne (by omega)]
  · rw [dite_eq_right (by simp; omega), dite_eq_right (by omega)]

/-- Reading index `j` after dropping `n` elements reads index `j + n` of the sequence; for a
negative `n`, `drop` pads with default values, which read back as the default. -/
private theorem seqGet_drop {a : LSort} (s : List (SortDenote tcInterp a)) (n j : Int)
    (h0 : 0 ≤ j) :
    seqGet a a (if 0 ≤ n then s.drop n.toNat
      else List.replicate (-n).toNat (default : SortDenote tcInterp a) ++ s) j =
      seqGet a a s (j + n) := by
  unfold seqGet
  split
  · by_cases hs : (j + n).toNat < s.length
    · rw [dite_eq_left ⟨h0, by simp; omega⟩, dite_eq_left ⟨by omega, hs⟩]
      simp only [List.getElem_drop]
      congr 3; omega
    · rw [dite_eq_right (by simp; omega), dite_eq_right (by omega)]
  · by_cases hj : j < -n
    · rw [dite_eq_right (show ¬(0 ≤ j + n ∧ _) by omega)]
      rw [dite_eq_left ⟨h0, by simp; omega⟩]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    · by_cases hs : (j + n).toNat < s.length
      · rw [dite_eq_left ⟨h0, by simp; omega⟩, dite_eq_left ⟨by omega, hs⟩]
        rw [List.getElem_append_right (by simp; omega)]
        congr 3; simp; omega
      · rw [dite_eq_right (by simp; omega), dite_eq_right (by omega)]

/-! #### Axioms that hold in the model -/

/-- A formula is a well-typed closed Boolean formula that holds in the model under every
valuation. -/
@[reducible] def AxHolds (ax : LExpr T.mono) : Prop :=
  LExpr.HasTypeA [] ax .bool ∧
  ∀ (vt : TyVarVal) (fv : FreeVarVal T tcInterp) (h : LExpr.HasTypeA [] ax .bool),
    (LExpr.denote tcInterp opInterp fv vt .nil ax .bool h : Bool) = true

/-- Every formula of a list is well typed and holds in the model. -/
def AxOK (axs : List (LExpr T.mono)) : Prop := ∀ ax ∈ axs, AxHolds ax

/-- The empty list of axioms holds. -/
private theorem AxOK.nil : AxOK [] := fun _ h => absurd h List.not_mem_nil

/-- A list of axioms that is empty holds. -/
private theorem AxOK.of_eq_nil {axs : List (LExpr T.mono)} (h : axs = []) : AxOK axs :=
  h ▸ AxOK.nil

/-- A list of axioms holds when its head and its tail do. -/
private theorem AxOK.cons {e : LExpr T.mono} {l : List (LExpr T.mono)}
    (he : AxHolds e) (hl : AxOK l) : AxOK (e :: l) := by
  intro ax hax
  rcases List.mem_cons.mp hax with rfl | hax
  · exact he
  · exact hl ax hax

/-- The concatenation of two lists of axioms that hold holds. -/
private theorem AxOK.append {l1 l2 : List (LExpr T.mono)} (h1 : AxOK l1) (h2 : AxOK l2) :
    AxOK (l1 ++ l2) := by
  intro ax hax
  rcases List.mem_append.mp hax with hax | hax
  · exact h1 ax hax
  · exact h2 ax hax

/-- Renaming an operator into one with the same interpretation preserves an axiom's typing
and truth. -/
private theorem AxHolds.rename {«from» to : String} (hop : opInterp to = opInterp «from»)
    {e : LExpr T.mono} (he : AxHolds e) :
    AxHolds (e.substOps (Strata.Util.HMap.ofList
      [((⟨«from», ()⟩ : T.Identifier), fun ty => (.op (ExprSourceLoc.synthesized "factory") ⟨to,
          ()⟩ ty : LExpr T.mono))])) := by
  have hsm : OpRenaming opInterp (Strata.Util.HMap.ofList
      [((⟨«from», ()⟩ : T.Identifier), fun ty => (.op (ExprSourceLoc.synthesized "factory") ⟨to,
          ()⟩ ty : LExpr T.mono))]) := by
    intro name mk hf oty
    have hk := Strata.Util.HMap.mem_keys_ofList _ _ (Strata.Util.HMap.find?_mem_keys _ hf)
    have hv := Strata.Util.HMap.mem_values_ofList _ _ (Strata.Util.HMap.find?_mem_values _ hf)
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk hv
    subst hk hv
    exact ⟨ExprSourceLoc.synthesized "factory", _, rfl, hop⟩
  refine ⟨HasTypeA_substOps hsm he.1, fun vt fv h' => ?_⟩
  rw [denote_substOps hsm .nil (HasTypeA_of_substOps hsm h') h']
  exact he.2 vt fv _

/-- Renaming an operator throughout a list of axioms (`renameOpIn`) into one with the same
interpretation preserves the list's axioms. -/
private theorem AxOK.renameOpIn {«from» to : String} (hop : opInterp to = opInterp «from»)
    {axs : List (LExpr T.mono)} (h : AxOK axs) : AxOK (renameOpIn «from» to axs) := by
  intro ax hax
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hax
  exact AxHolds.rename hop (h e he)

/-- The classical decision of a proposition. Rewriting `decide` into `cdec` keeps the
proposition as the only argument, so unfolding sorts inside it cannot leave a stale copy
in a `Decidable` instance. -/
@[expose] noncomputable def cdec (p : Prop) : Bool := @decide p (Classical.propDecidable p)

/-- A classical `decide` is `cdec`. -/
private theorem decide_eq_cdec (p : Prop) : @decide p (Classical.propDecidable p) = cdec p := rfl

/-- `cdec p` is `true` exactly when `p` holds. -/
private theorem cdec_eq_true (p : Prop) : (cdec p = true) = p := classical_decide_eq_true

/-- Deciding the equality of carrier views is deciding the equality of the values. -/
private theorem cdec_toC {s : LSort} (x y : SortDenote tcInterp s) :
    cdec (toC x = toC y) = cdec (x = y) := by
  rw [show (toC x = toC y) = (x = y) from propext (toC_inj x y)]

/-- Rewrite the interpretation of one operator application of an axiom. -/
syntax "ax_rw_op" : tactic
macro_rules
  | `(tactic| ax_rw_op) => `(tactic| first
    | rw [opInterp_intGe]
    | rw [opInterp_intLt]
    | rw [opInterp_intLe]
    | rw [opInterp_intAdd]
    | rw [opInterp_intSub]
    | rw [opInterp_boolAnd]
    | rw [opInterp_boolOr]
    | rw [opInterp_boolNot]
    | rw [opInterp_mapConst]
    | rw [opInterp_select]
    | rw [opInterp_update]
    | rw [opInterp_setEmpty]
    | rw [opInterp_setContains]
    | rw [opInterp_setInsert]
    | rw [opInterp_setRemove]
    | rw [opInterp_setUnion]
    | rw [opInterp_setIntersect]
    | rw [opInterp_setDifference]
    | rw [opInterp_seqLength]
    | rw [opInterp_seqEmpty]
    | rw [opInterp_seqAppend]
    | rw [opInterp_seqSelect]
    | rw [opInterp_seqBuild]
    | rw [opInterp_seqUpdate]
    | rw [opInterp_seqContains]
    | rw [opInterp_seqTake]
    | rw [opInterp_seqDrop]
    | rw [opInterp_seqSelectBang])

/-- Unfold the sorts in the types of the goal's binders and values. -/
macro "ax_sorts" : tactic => `(tactic|
  dsimp only [TyDenote, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LConst.ty, denoteConst])

/-- Simplify reads of sequences built by the sequence operations, discharging the index
bounds with `omega`. -/
macro "seq_simp" : tactic => `(tactic|
  simp (disch := omega) [seqGet_take, seqGet_append_left, seqGet_append_right,
    seqGet_append_last, seqGet_set_same, seqGet_set_ne, seqGet_drop, coe_self, coeS_self,
    ofC_toC])

/-- Close an axiom: check its typing by evaluating `typeCheck`, then peel its universal
quantifiers, compute its value, rewrite the interpretations of its operators, and simplify. -/
macro "ax_close" : tactic => `(tactic| (
  refine ⟨LExpr.typeCheck_to_HasTypeA rfl, ?_⟩
  intro vt fv h
  repeat (apply denote_true_of_Denotes; denotes; rw [classical_decide_eq_true]; ax_sorts; intro _)
  apply denote_true_of_Denotes
  · denotes
  repeat rw [decide_eq_cdec]
  ax_sorts
  repeat ax_rw_op
  repeat (first
    | rw [decide_eq_cdec] | rw [coe_self] | rw [coe_self_fun] | rw [coeS_self]
    | rw [coeS_self_fun] | rw [ofC_toC]
    | rw [toC_ofC] | rw [cdec_toC])
  try rw [cdec_eq_true]
  try rfl
  try simp (config := { contextual := true }) [cdec, toC_inj]
  try (intros; subst_vars; first
    | omega
    | (show ((_ : Int) = _); omega)
    | (seq_simp; done)
    | (split <;> seq_simp <;> omega))))

/-- Split a hypothesis `ax = e₁ ∨ … ∨ ax = eₙ` and prove each axiom. -/
macro "ax_cases" hax:ident : tactic => `(tactic| (
  repeat' (first | subst $hax:ident | rcases $hax:ident with $hax:ident | $hax:ident)
  all_goals ax_close))

/- Operator values are curried functions only up to unfolding `SortDenote`, so the
statements the axioms reduce to type-check only with these definitions unfolded, which
`simp` requires. They are made reducible for the rest of this namespace. -/
set_option allowUnsafeReducibility true in
attribute [local reducible] SortDenote Carrier tcInterp

/-- `withSelectBang` adds the `Sequence.select!` copies of a list of axioms, which hold
whenever the originals do. -/
private theorem AxOK.withSelectBang {axs : List (LExpr T.mono)} (h : AxOK axs) :
    AxOK (withSelectBang axs) :=
  AxOK.append h (AxOK.renameOpIn opInterp_seqSelectBang h)

/-- Every axiom of `mapConst` holds in the model. -/
private theorem ax_mapConst : AxOK mapConstFunc.func.axioms := by
  intro ax hax
  simp only [mapConstFunc, polyLitOp, List.mem_cons, List.not_mem_nil, or_false] at hax
  subst hax
  refine ⟨LExpr.typeCheck_to_HasTypeA rfl, ?_⟩
  intro vt fv h
  repeat (apply denote_true_of_Denotes; denotes; rw [classical_decide_eq_true]; ax_sorts; intro _)
  apply denote_true_of_Denotes
  · denotes
  rw [classical_decide_eq_true]
  ax_sorts
  rw [opInterp_select]
  rw [opInterp_mapConst]
  simp

/-- Every axiom of `update` holds in the model. -/
private theorem ax_mapUpdate : AxOK mapUpdateFunc.func.axioms := by
  intro ax hax
  simp only [mapUpdateFunc, polyLitOp, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.empty` holds in the model. -/
private theorem ax_setEmpty : AxOK setEmptyFunc.func.axioms := by
  intro ax hax
  simp only [setEmptyFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.insert` holds in the model. -/
private theorem ax_setInsert : AxOK setInsertFunc.func.axioms := by
  intro ax hax
  simp only [setInsertFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.remove` holds in the model. -/
private theorem ax_setRemove : AxOK setRemoveFunc.func.axioms := by
  intro ax hax
  simp only [setRemoveFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.union` holds in the model. -/
private theorem ax_setUnion : AxOK setUnionFunc.func.axioms := by
  intro ax hax
  simp only [setUnionFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.intersect` holds in the model. -/
private theorem ax_setIntersect : AxOK setIntersectFunc.func.axioms := by
  intro ax hax
  simp only [setIntersectFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Set.difference` holds in the model. -/
private theorem ax_setDifference : AxOK setDifferenceFunc.func.axioms := by
  intro ax hax
  simp only [setDifferenceFunc, polyUneval, List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Sequence.length` holds in the model. -/
private theorem ax_seqLength : AxOK seqLengthFunc.func.axioms := by
  intro ax hax
  simp only [seqLengthFunc, polyLitOp, Int.ofNat_eq_natCast, Int.cast_ofNat_Int, List.mem_cons,
    List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- Every axiom of `Sequence.empty` holds in the model. -/
private theorem ax_seqEmpty : AxOK seqEmptyFunc.func.axioms := by
  intro ax hax
  simp only [seqEmptyFunc, polyLitOp, Int.ofNat_eq_natCast, Int.cast_ofNat_Int, List.mem_cons,
    List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- The only axiom of `Sequence.select`, the agreement of `Sequence.select!` with it in range,
holds in the model. -/
private theorem ax_seqSelect : AxOK seqSelectFunc.func.axioms := by
  intro ax hax
  simp only [seqSelectFunc, polyLitOp, Int.ofNat_eq_natCast, Int.cast_ofNat_Int,
    List.mem_cons, List.not_mem_nil, or_false] at hax
  ax_cases hax

/-- The `i`-th axiom of a built-in function, used to prove a long axiom list one axiom per
theorem. -/
private abbrev axAt (wf : WFLFunc CoreLParams) (i : Nat) : LExpr T.mono := wf.func.axioms[i]!

/-- Unfold `axAt` on a function whose axioms are `[length axiom] ++ withSelectBang [...]`,
down to the axiom itself, without computing the renamed copies. -/
macro "ax_at" fn:ident : tactic => `(tactic| (
  simp only [axAt, $fn:ident, polyLitOp, withSelectBang, List.cons_append, List.nil_append,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  ax_close))

/-- The `Sequence.append` axiom `length(append(s, t)) == length(s) + length(t)` holds in the
model. -/
private theorem ax_seqAppend_0 : AxHolds (axAt seqAppendFunc 0) := by ax_at seqAppendFunc

/-- The `Sequence.append` axiom stating that selecting inside the first sequence of an append
selects in it holds in the model. -/
private theorem ax_seqAppend_1 : AxHolds (axAt seqAppendFunc 1) := by ax_at seqAppendFunc

/-- The `Sequence.append` axiom stating that selecting past the first sequence of an append
selects in the second, at the index shifted by the first's length holds in the model. -/
private theorem ax_seqAppend_2 : AxHolds (axAt seqAppendFunc 2) := by ax_at seqAppendFunc

/-- Every axiom of `Sequence.append` holds in the model. -/
private theorem ax_seqAppend : AxOK seqAppendFunc.func.axioms := by
  rw [show seqAppendFunc.func.axioms =
      [axAt seqAppendFunc 0] ++ withSelectBang [axAt seqAppendFunc 1, axAt seqAppendFunc 2]
        from rfl]
  exact AxOK.append (AxOK.cons ax_seqAppend_0 AxOK.nil)
    (AxOK.withSelectBang (AxOK.cons ax_seqAppend_1 (AxOK.cons ax_seqAppend_2 AxOK.nil)))

/-- The `Sequence.build` axiom `length(build(s, v)) == 1 + length(s)` holds in the model. -/
private theorem ax_seqBuild_0 : AxHolds (axAt seqBuildFunc 0) := by ax_at seqBuildFunc

/-- The `Sequence.build` axiom stating that selecting at `length(s)` in `build(s, v)` gives `v`
holds in the model. -/
private theorem ax_seqBuild_1 : AxHolds (axAt seqBuildFunc 1) := by ax_at seqBuildFunc

/-- The `Sequence.build` axiom stating that selecting at an in-range index of `s` in `build(s, v)`
selects in `s` holds in the model. -/
private theorem ax_seqBuild_2 : AxHolds (axAt seqBuildFunc 2) := by ax_at seqBuildFunc

/-- Every axiom of `Sequence.build` holds in the model. -/
private theorem ax_seqBuild : AxOK seqBuildFunc.func.axioms := by
  rw [show seqBuildFunc.func.axioms =
      [axAt seqBuildFunc 0] ++ withSelectBang [axAt seqBuildFunc 1, axAt seqBuildFunc 2]
        from rfl]
  exact AxOK.append (AxOK.cons ax_seqBuild_0 AxOK.nil)
    (AxOK.withSelectBang (AxOK.cons ax_seqBuild_1 (AxOK.cons ax_seqBuild_2 AxOK.nil)))

/-- The `Sequence.update` axiom `length(update(s, i, v)) == length(s)` holds in the model. -/
private theorem ax_seqUpdate_0 : AxHolds (axAt seqUpdateFunc 0) := by ax_at seqUpdateFunc

/-- The `Sequence.update` axiom stating that selecting at an in-range `i` in `update(s, i, v)`
gives `v` holds in the model. -/
private theorem ax_seqUpdate_1 : AxHolds (axAt seqUpdateFunc 1) := by ax_at seqUpdateFunc

/-- The `Sequence.update` axiom stating that selecting at an in-range index other than `i` in
`update(s, i, v)` selects in `s` holds in the model. -/
private theorem ax_seqUpdate_2 : AxHolds (axAt seqUpdateFunc 2) := by ax_at seqUpdateFunc

/-- Every axiom of `Sequence.update` holds in the model. -/
private theorem ax_seqUpdate : AxOK seqUpdateFunc.func.axioms := by
  rw [show seqUpdateFunc.func.axioms =
      [axAt seqUpdateFunc 0] ++ withSelectBang [axAt seqUpdateFunc 1, axAt seqUpdateFunc 2]
        from rfl]
  exact AxOK.append (AxOK.cons ax_seqUpdate_0 AxOK.nil)
    (AxOK.withSelectBang (AxOK.cons ax_seqUpdate_1 (AxOK.cons ax_seqUpdate_2 AxOK.nil)))

/-- Every axiom of `Sequence.update!` holds in the model. -/
private theorem ax_seqUpdateBang : AxOK seqUpdateUnsafeFunc.func.axioms := by
  simp only [seqUpdateUnsafeFunc, polyLitOp]
  exact AxOK.renameOpIn opInterp_seqUpdateBang ax_seqUpdate

/-- The `Sequence.contains` axiom, `contains(s, v)` iff some in-range index selects `v`,
holds in the model. -/
private theorem ax_seqContains_0 : AxOK [axAt seqContainsFunc 0] := by
  intro ax hax
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
  subst hax
  simp only [axAt, seqContainsFunc, polyLitOp, withSelectBang, List.cons_append,
    List.nil_append, List.getElem!_cons_zero, Int.ofNat_eq_natCast, Int.cast_ofNat_Int]
  ax_close
  -- The right-hand side is an existential whose body is still a `denote`: compute it
  -- under the binder.
  refine congrArg (fun p => @decide p (Classical.propDecidable p)) (propext ?_)
  refine Iff.symm (exists_congr fun i => ?_)
  apply Iff.trans (Eq.to_iff (denote_true_iff_of_Denotes ?hd))
  case hd => denotes
  repeat rw [decide_eq_cdec]
  ax_sorts
  repeat ax_rw_op
  simp [cdec, and_assoc]

/-- Every axiom of `Sequence.contains` holds in the model: the axiom above and its
`Sequence.select!` copy. -/
private theorem ax_seqContains : AxOK seqContainsFunc.func.axioms := by
  rw [show seqContainsFunc.func.axioms = withSelectBang [axAt seqContainsFunc 0] from rfl]
  exact AxOK.withSelectBang ax_seqContains_0

/-- The `Sequence.take` axiom for `0 <= n <= length(s)`, `length(take(s, n)) == n` holds in the
model. -/
private theorem ax_seqTake_0 : AxHolds (axAt seqTakeFunc 0) := by ax_at seqTakeFunc

/-- The `Sequence.take` axiom stating that selecting at `0 <= j < n` in `take(s, n)` selects in
`s` holds in the model. -/
private theorem ax_seqTake_1 : AxHolds (axAt seqTakeFunc 1) := by ax_at seqTakeFunc

/-- Every axiom of `Sequence.take` holds in the model. -/
private theorem ax_seqTake : AxOK seqTakeFunc.func.axioms := by
  rw [show seqTakeFunc.func.axioms =
      [axAt seqTakeFunc 0] ++ withSelectBang [axAt seqTakeFunc 1] from rfl]
  exact AxOK.append (AxOK.cons ax_seqTake_0 AxOK.nil)
    (AxOK.withSelectBang (AxOK.cons ax_seqTake_1 AxOK.nil))

/-- Every axiom of `Sequence.take!` holds in the model. -/
private theorem ax_seqTakeBang : AxOK seqTakeUnsafeFunc.func.axioms := by
  simp only [seqTakeUnsafeFunc, polyLitOp]
  exact AxOK.renameOpIn opInterp_seqTakeBang ax_seqTake

/-- The `Sequence.drop` axiom for `0 <= n <= length(s)`, `length(drop(s, n)) == length(s) - n`
holds in the model. -/
private theorem ax_seqDrop_0 : AxHolds (axAt seqDropFunc 0) := by ax_at seqDropFunc

/-- The `Sequence.drop` axiom stating that selecting at an in-range `j` in `drop(s, n)` selects in
`s` at `j + n` holds in the model. -/
private theorem ax_seqDrop_1 : AxHolds (axAt seqDropFunc 1) := by ax_at seqDropFunc

/-- Every axiom of `Sequence.drop` holds in the model. -/
private theorem ax_seqDrop : AxOK seqDropFunc.func.axioms := by
  rw [show seqDropFunc.func.axioms =
      [axAt seqDropFunc 0] ++ withSelectBang [axAt seqDropFunc 1] from rfl]
  exact AxOK.append (AxOK.cons ax_seqDrop_0 AxOK.nil)
    (AxOK.withSelectBang (AxOK.cons ax_seqDrop_1 AxOK.nil))

/-- Every axiom of `Sequence.drop!` holds in the model. -/
private theorem ax_seqDropBang : AxOK seqDropUnsafeFunc.func.axioms := by
  simp only [seqDropUnsafeFunc, polyLitOp]
  exact AxOK.renameOpIn opInterp_seqDropBang ax_seqDrop

/-- Every axiom of every built-in function is well typed and holds in the model. The proof
discharges each built-in function individually, so an axiom added to the factory fails this
proof until it is proved too. -/
private theorem all_axOK : ∀ wf ∈ Core.WFFactoryArray.toList, AxOK wf.func.axioms := by
  unfold Core.WFFactoryArray
  simp only [Array.toList_appendList, List.forall_mem_append]
  repeat' apply And.intro
  all_goals
    repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
    exact List.forall_mem_nil _
  all_goals
    first
    | exact AxOK.of_eq_nil rfl
    | exact ax_mapConst
    | exact ax_mapUpdate
    | exact ax_setEmpty
    | exact ax_setInsert
    | exact ax_setRemove
    | exact ax_setUnion
    | exact ax_setIntersect
    | exact ax_setDifference
    | exact ax_seqLength
    | exact ax_seqEmpty
    | exact ax_seqSelect
    | exact ax_seqAppend
    | exact ax_seqBuild
    | exact ax_seqUpdate
    | exact ax_seqUpdateBang
    | exact ax_seqContains
    | exact ax_seqTake
    | exact ax_seqTakeBang
    | exact ax_seqDrop
    | exact ax_seqDropBang

/-- The axioms of the factory function named `f`, which is in `Core.Factory`, are those of an
entry of `Core.WFFactoryArray`, so `all_axOK` covers them. -/
private theorem axOK_of_mem (f : String) (hf : f ∈ Core.Factory) :
    AxOK (Core.Factory[f]).axioms := by
  have hmem : Core.Factory[f] ∈ Core.WFFactoryArray.map (·.func) :=
    Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) (get_mem f hf)
  obtain ⟨wf, hwf, hfn⟩ := Array.mem_map.mp hmem
  rw [← hfn]
  exact all_axOK wf (Array.mem_def.mp hwf)

/-- Every axiom of `Core.Factory` holds in the model. -/
private theorem axioms_satisfied : Factory.AxiomsSatisfied tcInterp opInterp Core.Factory :=
  fun f hf ax hax => (axOK_of_mem f hf ax hax).2

/-- Every axiom of `Core.Factory` is well typed as a closed Boolean formula, so
`Factory.AxiomsSatisfied` constrains all of them. -/
private theorem axioms_wellTyped :
    ∀ (f : String) (hf : f ∈ Core.Factory), ∀ ax ∈ (Core.Factory[f]).axioms,
      LExpr.HasTypeA [] ax .bool :=
  fun f hf ax hax => (axOK_of_mem f hf ax hax).1

/-- The evaluator-backed interpretation used to define the public Core model. -/
noncomputable def model : Interp Core.Factory where
  tcInterp := tcInterp
  opInterp := opInterp
  allInhabited := instAllInhab
  interpConsistent := ⟨bodies_consistent, eval_consistent⟩
  axiomsSatisfied := axioms_satisfied
  constrConsistent := constr_consistent

end FactoryInterpModel

open Classical in
/-- **An operator interpretation gives the real operations their SMT-LIB meaning.** The
    SMT encoder sends `Real.Add`, `Real.Sub`, `Real.Mul`, `Real.Div`, `Real.Neg`,
    `Real.Lt`, `Real.Le`, `Real.Gt` and `Real.Ge` to the operations of the SMT-LIB theory
    of reals, while `Core.Factory` gives them no evaluator and no axiom, so nothing else
    constrains them in a model. This states that `op` interprets each as the
    corresponding operation of `Strata.Util.Real`, the carrier of `real`, at every
    argument. Division is constrained only at a nonzero divisor: SMT-LIB makes `x / 0`
    some unspecified real for each `x`. `factoryInterp` happens to make it `0`; a back end
    may assume this predicate, not that value.

    Core's real carrier is `Strata.Util.Real`, a complete ordered field (proved:
    `Strata.Util.Real.exists_isLUB`), as the reals of SMT-LIB's theory are. That the solver
    decides that theory correctly is not proved: it is part of the solver's trusted
    specification, as for every other theory.

    It is stated on the operator interpretation rather than on an `Interp` of a given
    factory, so it applies as is to a model of any extension of `Core.Factory`, such as
    the factory of a program with its own functions and datatypes: write
    `RealsAsReal I.opInterp`. -/
structure RealsAsReal {tcInterp : TyConstrInterp} (op : OpInterp tcInterp) : Prop where
  add : op "Real.Add" (realBinSort .real) = fun (x y : Strata.Util.Real) => x + y
  sub : op "Real.Sub" (realBinSort .real) = fun (x y : Strata.Util.Real) => x - y
  mul : op "Real.Mul" (realBinSort .real) = fun (x y : Strata.Util.Real) => x * y
  div : ∀ x y : Strata.Util.Real, y ≠ 0 →
    (op "Real.Div" (realBinSort .real) : Strata.Util.Real → Strata.Util.Real → Strata.Util.Real) x y = x / y
  neg : op "Real.Neg" (.tcons "arrow" [.real, .real]) = fun (x : Strata.Util.Real) => -x
  lt : op "Real.Lt" (realBinSort .bool) = fun (x y : Strata.Util.Real) => decide (x < y)
  le : op "Real.Le" (realBinSort .bool) = fun (x y : Strata.Util.Real) => decide (x ≤ y)
  gt : op "Real.Gt" (realBinSort .bool) = fun (x y : Strata.Util.Real) => decide (x > y)
  ge : op "Real.Ge" (realBinSort .bool) = fun (x y : Strata.Util.Real) => decide (x ≥ y)

/-- A sound, consistent interpretation of `Core.Factory`. -/
noncomputable def factoryInterp : Lambda.Interp Core.Factory :=
  FactoryInterpModel.model

/-- Every axiom of `Core.Factory` holds in the concrete Core interpretation, so the
    axioms are jointly satisfiable. -/
theorem factoryInterp_axiomsSatisfied :
    Lambda.Factory.AxiomsSatisfied factoryInterp.tcInterp factoryInterp.opInterp
      Core.Factory :=
  factoryInterp.axiomsSatisfied

/-- Every axiom of `Core.Factory` is well typed as a closed Boolean formula, so
`factoryInterp_axiomsSatisfied` covers every axiom, none vacuously. -/
theorem factory_axioms_wellTyped :
    ∀ (f : String) (hf : f ∈ Core.Factory), ∀ ax ∈ (Core.Factory[f]).axioms,
      LExpr.HasTypeA [] ax .bool :=
  FactoryInterpModel.axioms_wellTyped

/-- The concrete Core interpretation agrees with every body and concrete evaluator in
    `Core.Factory`. -/
theorem factoryInterp_interpConsistent :
    Lambda.Factory.InterpConsistent factoryInterp.tcInterp factoryInterp.opInterp
      Core.Factory :=
  factoryInterp.interpConsistent

/-- `Core.Factory` admits a consistent interpretation. -/
theorem factoryInterp_nonempty : Nonempty (Lambda.Interp Core.Factory) := ⟨factoryInterp⟩

open FactoryInterpModel in
/-- The concrete Core interpretation gives the real operations their SMT-LIB meaning, so
    `RealsAsReal` is satisfiable together with the factory's other constraints. -/
theorem factoryInterp_realsAsReal : RealsAsReal factoryInterp.opInterp where
  add := opInterp_realAdd
  sub := opInterp_realSub
  mul := opInterp_realMul
  div x y _ := congrFun (congrFun opInterp_realDiv x) y
  neg := opInterp_realNeg
  lt := opInterp_realLt
  le := opInterp_realLe
  gt := opInterp_realGt
  ge := opInterp_realGe

/-- The concrete interpretation's `Real.Add` is addition on `Real` at every argument, irrational
    ones included: the real operations are defined directly as operations of `Real`, not through
    a concrete evaluator on literals. -/
theorem factoryInterp_realAdd (x y : Strata.Util.Real) :
    (factoryInterp.opInterp "Real.Add" (realBinSort .real) : Strata.Util.Real → Strata.Util.Real → Strata.Util.Real) x y = x + y := by
  rw [factoryInterp_realsAsReal.add]

end

end Core
