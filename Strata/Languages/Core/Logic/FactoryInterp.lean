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

/-!
## A Sound Interpretation of `Core.Factory`

This module builds a concrete, consistent `Lambda.Interp Core.Factory` and the
witness `Nonempty (Lambda.Interp Core.Factory)`.

The primary entry points are:
- `Core.factoryInterp : Lambda.Interp Core.Factory`
- `Core.factoryInterp_interpConsistent` exposes its factory-consistency proof
- `Core.factoryInterp_nonempty : Nonempty (Lambda.Interp Core.Factory)`

Implementation declarations live under `Core.FactoryInterpModel`.
-/

open Lambda

namespace Core

public section

namespace FactoryInterpModel

/-- Core's Lambda expression parameters. -/
abbrev T : LExprParams := Core.CoreLParams

/-- Custom type constructors map to `Unit`; primitives are handled by `SortDenote`. -/
@[expose] def tcInterp : TyConstrInterp := fun _ _ => Unit

/-- Every custom type interpretation is inhabited by `()`. -/
instance instAllInhab : TyConstrInterp.AllInhabited tcInterp := ⟨fun _ _ => ⟨()⟩⟩

/-- Reify a primitive semantic value as a Core literal. -/
@[expose] def reifyAt : (s : LSort) → SortDenote tcInterp s → LExpr T.mono
  | .tcons "bool" [],   v => .const default (.boolConst v)
  | .tcons "int" [],    v => .const default (.intConst v)
  | .tcons "real" [],   v => .const default (.rationalConst v)
  | .tcons "string" [], v => .const default (.strConst v)
  | .bitvec n,          v => .const default (.bitvecConst n v)
  | .tcons "arrow" [_, _], _ => .const default (.boolConst false)
  | .tcons _ _, _ => .const default (.boolConst false)

/-- Decode a Core literal as a semantic value, defaulting for unsupported forms. -/
@[expose] def decodeAt : (s : LSort) → Option (LExpr T.mono) → SortDenote tcInterp s
  | .tcons "bool" [],   some (.const _ (.boolConst b)) => b
  | .tcons "int" [],    some (.const _ (.intConst i))  => i
  | .tcons "real" [],   some (.const _ (.rationalConst r)) => r
  | .tcons "string" [], some (.const _ (.strConst s)) => s
  | .bitvec n,          some (.const _ (.bitvecConst n' b)) =>
      if h : n = n' then h ▸ b else default
  | s, _ => (SortDenote.instInhabited s).default

/-- Lift a concrete evaluator to a curried semantic value at the requested sort. -/
@[expose] def gatherEval
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (acc : List (LExpr T.mono)) : (s : LSort) → SortDenote tcInterp s
  | .tcons "arrow" [a, b] => fun (x : SortDenote tcInterp a) =>
      gatherEval ceval (acc ++ [reifyAt a x]) b
  | .tcons "bool" [] => decodeAt (.tcons "bool" []) (ceval default acc)
  | .tcons "int" [] => decodeAt (.tcons "int" []) (ceval default acc)
  | .tcons "real" [] => decodeAt (.tcons "real" []) (ceval default acc)
  | .tcons "string" [] => decodeAt (.tcons "string" []) (ceval default acc)
  | .bitvec n => decodeAt (.bitvec n) (ceval default acc)
  | .tcons nm args => decodeAt (.tcons nm args) (ceval default acc)

/-! Equations for `gatherEval` at the primitive output sorts. Lean cannot generate
`gatherEval`'s equation lemmas automatically, so we state the cases used below
directly. -/

theorem gatherEval_bool
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "bool" []) =
      decodeAt (.tcons "bool" []) (ceval default acc) := rfl

theorem gatherEval_int
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "int" []) =
      decodeAt (.tcons "int" []) (ceval default acc) := rfl

theorem gatherEval_string
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (acc : List (LExpr T.mono)) :
    gatherEval ceval acc (.tcons "string" []) =
      decodeAt (.tcons "string" []) (ceval default acc) := rfl

theorem gatherEval_bitvec
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (acc : List (LExpr T.mono)) (n : Nat) :
    gatherEval ceval acc (.bitvec n) =
      decodeAt (.bitvec n) (ceval default acc) := rfl

/-- The dynamic operator interpretation: look up the factory function by name
and, if it has a `concreteEval`, build its denotation by reifying arguments,
calling `concreteEval`, and decoding the result. -/
@[expose] def opInterp : OpInterp tcInterp :=
  fun name s =>
    match Core.Factory.get? name with
    | none => (SortDenote.instInhabited s).default
    | some func =>
      match func.concreteEval with
      | none => (SortDenote.instInhabited s).default
      | some ceval => gatherEval ceval [] s

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
        = decodeAt (LMonoTy.substTyVars vt outTy) (ceval default acc)
  /-- Denoting a built constant equals decoding it (metadata-insensitive). -/
  denote_decode : ∀ (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
      (md md' : T.Metadata) (w : OutV) (h : LExpr.HasTypeA [] (mkOut md w) outTy),
      LExpr.denote tcInterp opInterp fvarVal vt .nil (mkOut md w) outTy h
        = decodeAt (LMonoTy.substTyVars vt outTy) (some (mkOut md' w))

/-- Generic `concreteEval` consistency for a unary op over primitive types. -/
private theorem unaryOp_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type}
    (func : LFunc T)
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (hin : (List.map Prod.snd func.inputs) = [inTy])
    (hout : func.output = outTy)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    [ip : InPrim inTy InV] [op : OutPrim outTy OutV]
    (f : InV → OutV)
    (hbeh : ∀ md x, ceval md [x] =
      (match InPrim.cevalIn (inTy := inTy) x with
       | some a => some (OutPrim.mkOut (outTy := outTy) md (f a))
       | _ => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr heval
  simp only []
  intro h_args h_result
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
    rw [hbeh md a] at heval
    cases hca : InPrim.cevalIn (inTy := inTy) a with
    | none => rw [hca] at heval; simp at heval
    | some av =>
      rw [hca] at heval
      simp only [Option.some.injEq] at heval
      subst heval
      simp only [opInterp, hlook, hce, denoteArgs]
      show LExpr.denote tcInterp opInterp fvarVal vt HList.nil (OutPrim.mkOut outTy md (f av)) outTy h_result
          = gatherEval ceval [reifyAt (LMonoTy.substTyVars vt inTy)
              (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a inTy hx)] (LMonoTy.substTyVars vt outTy)
      rw [OutPrim.gather_eq, hbeh default, InPrim.reify_ceval fvarVal vt a hx av hca]
      rw [OutPrim.denote_decode fvarVal vt md default (f av) h_result]

/-- Generic `concreteEval` consistency for a binary op over primitive types.
Both inputs share type `inTy`; `guard` is checked on the second argument. -/
private theorem binaryOp_consistent
    {inTy outTy : LMonoTy} {InV OutV : Type}
    (func : LFunc T)
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (hin : (List.map Prod.snd func.inputs) = [inTy, inTy])
    (hout : func.output = outTy)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    [ip : InPrim inTy InV] [opr : OutPrim outTy OutV]
    (g : InV → InV → OutV) (guard : InV → Bool)
    (hbeh : ∀ md x y, ceval md [x, y] =
      (match InPrim.cevalIn (inTy := inTy) x, InPrim.cevalIn (inTy := inTy) y with
       | some a, some b => if guard b then some (OutPrim.mkOut (outTy := outTy) md (g a b)) else none
       | _, _ => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr heval
  simp only []
  intro h_args h_result
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
      rw [hbeh md a a2] at heval
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
            simp only [opInterp, hlook, hce, denoteArgs]
            show LExpr.denote tcInterp opInterp fvarVal vt HList.nil
                  (OutPrim.mkOut outTy md (g av bv)) outTy h_result
                = gatherEval ceval
                    [reifyAt (LMonoTy.substTyVars vt inTy)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a inTy hx),
                     reifyAt (LMonoTy.substTyVars vt inTy)
                        (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a2 inTy hy)]
                    (LMonoTy.substTyVars vt outTy)
            rw [OutPrim.gather_eq, hbeh default,
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
    (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (hin : (List.map Prod.snd func.inputs) = [LMonoTy.bool, LMonoTy.bool])
    (hout : func.output = LMonoTy.bool)
    (hce : func.concreteEval = some ceval)
    (hlook : Core.Factory.get? func.name.name = some func)
    (absorb decided : Bool)
    (hbeh : ∀ md x y, ceval md [x, y] =
      (match InPrim.cevalIn (inTy := LMonoTy.bool) x with
       | some a =>
         if a == absorb then some (OutPrim.mkOut (outTy := LMonoTy.bool) md decided) else some y
       | none => none)) :
    LFunc.InterpConsistentEval tcInterp opInterp func ceval := by
  intro vt fvarVal md tySubst argExprs resultExpr heval
  simp only []
  intro h_args h_result
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
      rw [hbeh md a a2] at heval
      cases hca : InPrim.cevalIn (inTy := LMonoTy.bool) a with
      | none => rw [hca] at heval; simp at heval
      | some av =>
        rw [hca] at heval
        simp only [opInterp, hlook, hce, denoteArgs]
        show LExpr.denote tcInterp opInterp fvarVal vt HList.nil resultExpr LMonoTy.bool h_result
            = gatherEval ceval
                [reifyAt (LMonoTy.substTyVars vt LMonoTy.bool)
                    (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a LMonoTy.bool hx),
                 reifyAt (LMonoTy.substTyVars vt LMonoTy.bool)
                    (LExpr.denote tcInterp opInterp fvarVal vt HList.nil a2 LMonoTy.bool hy)]
                (LMonoTy.substTyVars vt LMonoTy.bool)
        rw [OutPrim.gather_eq (outTy := LMonoTy.bool), hbeh default,
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
    {n : T.Identifier} {f : InV → OutV} {pre hI hO hp}
    {ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)}
    (hce : (unaryOp n f pre hI hO hp).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (unaryOp n f pre hI hO hp).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (unaryOp n f pre hI hO hp).func ceval := by
  injection hce with hce
  subst hce
  refine unaryOp_consistent (inTy := inTy) (outTy := outTy) _ _ rfl rfl rfl hlook f ?_
  intro md x
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
    {ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)}
    (hce : (binaryOp n g guard pre hI hO hp).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (binaryOp n g guard pre hI hO hp).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (binaryOp n g guard pre hI hO hp).func ceval := by
  injection hce with hce
  subst hce
  refine binaryOp_consistent (inTy := inTy) (outTy := outTy) _ _ rfl rfl rfl hlook g guard ?_
  intro md x y
  rw [hcin, hmk]
  rfl

/-- `concreteEval` consistency for any `shortCircuitOp`-built function.
Stated over `shortCircuitOp` itself so a factory entry unifies with it directly. -/
private theorem shortCircuit_func_consistent
    {n : T.Identifier} {absorb decided : Bool}
    {ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)}
    (hce : (shortCircuitOp n absorb decided).func.concreteEval = some ceval)
    (hlook : Core.Factory.get? n.name = some (shortCircuitOp n absorb decided).func) :
    LFunc.InterpConsistentEval tcInterp opInterp (shortCircuitOp n absorb decided).func ceval := by
  injection hce with hce
  subst hce
  exact shortCircuit_consistent _ _ rfl rfl rfl hlook absorb decided (by intro md x y; rfl)

/-- For every `Core.Factory` function with a concrete evaluator, `opInterp` agrees
    with that evaluator. -/
private theorem eval_consistent :
    ∀ (f : String), (hf : f ∈ Core.Factory) → ∀ ceval, (Core.Factory[f]).concreteEval = some ceval →
      LFunc.InterpConsistentEval tcInterp opInterp (Core.Factory[f]) ceval := by
  -- Each entry is either evaluator-free or built by `unaryOp`/`binaryOp`.
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
      | exact unaryOp_func_consistent (hce := hce) (hlook := hlook)
      | exact shortCircuit_func_consistent (hce := hce) (hlook := hlook)
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
  constructor
  · intro f1 _ hf1 _ hc1 _ _ _; exact absurd hc1 (by rw [all_not_constr f1 hf1]; simp)
  · intro f hf hc; exact absurd hc (by rw [all_not_constr f hf]; simp)

/-- The evaluator-backed interpretation used to define the public Core model. -/
def model : Interp Core.Factory where
  tcInterp := tcInterp
  opInterp := opInterp
  allInhabited := instAllInhab
  interpConsistent := ⟨bodies_consistent, eval_consistent⟩
  constrConsistent := constr_consistent

end FactoryInterpModel

/-- A sound, consistent interpretation of `Core.Factory`. -/
def factoryInterp : Lambda.Interp Core.Factory :=
  FactoryInterpModel.model

/-- The concrete Core interpretation agrees with every body and concrete evaluator in
    `Core.Factory`. -/
theorem factoryInterp_interpConsistent :
    Lambda.Factory.InterpConsistent factoryInterp.tcInterp factoryInterp.opInterp
      Core.Factory :=
  factoryInterp.interpConsistent

/-- `Core.Factory` admits a consistent interpretation. -/
theorem factoryInterp_nonempty : Nonempty (Lambda.Interp Core.Factory) := ⟨factoryInterp⟩

end

end Core
