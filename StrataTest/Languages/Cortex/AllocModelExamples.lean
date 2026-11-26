/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Cortex.SafeRefsProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.IntEvalProps
import Strata.DL.Imperative.CmdSemanticsProps
import all StrataTest.Languages.Cortex.HeapModelHelpers
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Cortex.Semantics
import all Strata.Languages.Cortex.LangDef
import all Strata.Languages.Cortex.Module
import all Strata.Languages.Cortex.AST

/-! # A lawful heap model in which objects are allocated, and a run that allocates

The heap laws `HeapApiModel` and `RefTagModel` do not say that allocation is possible. This
file gives a lawful model of both in which it is, and derives a run of the relation that
allocates an object and reads its fields.

The model: a reference is `none` (`Null`) or `some a` (`Obj(a, t)`), every tag is the unit
value, and a heap is an allocation counter `n` with one total map per field. The allocated
references are the `Obj(a, t)` with `0 ≤ a < n`. A location set is a set of pairs of a
reference and a field identity; `Heap.onlyModifies` compares the field maps only, so an
allocation, which changes only the counter, modifies no location.

The program has one composite, `Box { v : int, next : Box }`, and one procedure, `main`,
whose body declares `x : Box`, `y : int` and `z : Box`, then runs `x := new Box`,
`y := x#v` and `z := x#next`.

## Key results

- `heapApi`, `refTag`: the model satisfies the heap laws and the reference laws of every
  program whose fields are among `Box.v : int` and `Box.next : Box`.
- `newObj_model`, `newObj_exists`: in every heap of the model, `new Box` can allocate the
  reference `Obj(n, Box$Tag)` of the counter `n`.
- `initEnvWF_alloc`: `CortexInitEnvWF` holds for `main`.
- `alloc_run`: from that environment, the entry body of `main` runs to its end in
  `EventLang.cortex`, and ends with `x` the new object, `y = 0` and `z = Null`.
- `alloc_nonvacuous`: the premise holds and a run through `new` and `readField` reaches the
  end.
- `safeStart_alloc`: the runs of `main` start with safe references.
- `objProg_refused`, `mkRefProg_refused`: programs that write `Obj(5, Box$Tag)` or a reference
  from a function annotated to return one do not start with safe references.
- `noRefOp_annotation`: the check reads only an operator's annotation.
- `mapProg_noRefOps`: the check accepts a program that updates and reads a map.
-/

namespace Cortex.Sem.AllocModelExamples

open Imperative Lambda HeapModel

/-! ## The model -/

/-- A heap of the model: the allocation counter and the values of the fields `v` and `next`
of every reference. -/
private structure HeapV where
  count : Nat
  v : Option Int → Int
  next : Option Int → Option Int

/-- A reference is allocated in `h` when it is `Obj(a, t)` with `0 ≤ a < h.count`. -/
private def HeapV.alloc (h : HeapV) : Option Int → Bool
  | none => false
  | some a => decide (0 ≤ a ∧ a < h.count)

/-- The carriers of the sorts the model interprets: references, heaps, location sets and
field identities. -/
private def carrier : String → List LSort → Type
  | "Ref", [] => Option Int
  | "Heap", [] => HeapV
  | "Locs", [] => Option Int → Bool → Bool
  | "FieldId", [] => Bool
  | _, _ => Unit

private instance carrier_inhabited : TyConstrInterp.AllInhabited carrier where
  inhabited name args := by
    unfold carrier
    split
    · exact ⟨none⟩
    · exact ⟨⟨0, fun _ => 0, fun _ => none⟩⟩
    · exact ⟨fun _ _ => false⟩
    · exact ⟨false⟩
    · exact ⟨()⟩

/-- The interpretation of the operators. The field identity of `Box.v` is `false` and that
of `Box.next` is `true`. -/
private noncomputable def opI : (name : String) → (s : LSort) → SortDenote carrier s
  | "Bool.Not", .tcons "arrow" [.tcons "bool" [], .tcons "bool" []] => fun (b : Bool) => !b
  | "Null", .tcons "Ref" [] => (none : Option Int)
  | "Obj", .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "Tag" [], .tcons "Ref" []]] =>
    fun (a : Int) (_ : Unit) => (some a : Option Int)
  | "Ref..isObj", .tcons "arrow" [.tcons "Ref" [], .tcons "bool" []] =>
    fun (o : Option Int) => o.isSome
  | "Ref.tag", .tcons "arrow" [.tcons "Ref" [], .tcons "Tag" []] => fun (_ : Option Int) => ()
  | "Locs.none", .tcons "Locs" [] => fun (_ : Option Int) (_ : Bool) => false
  | "Heap.read", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "int" []], .tcons "int" []]]] =>
    fun (h : HeapV) (o : Option Int) (_ : Unit) => h.v o
  | "Heap.read", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "Ref" []], .tcons "Ref" []]]] =>
    fun (h : HeapV) (o : Option Int) (_ : Unit) => h.next o
  | "Heap.write", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "int" []], .tcons "arrow" [.tcons "int" [],
      .tcons "Heap" []]]]] =>
    fun (h : HeapV) (o : Option Int) (_ : Unit) (w : Int) =>
      ({ h with v := fun p => if p = o then w else h.v p } : HeapV)
  | "Heap.write", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "Ref" []], .tcons "arrow" [.tcons "Ref" [],
      .tcons "Heap" []]]]] =>
    fun (h : HeapV) (o : Option Int) (_ : Unit) (w : Option Int) =>
      ({ h with next := fun p => if p = o then w else h.next p } : HeapV)
  | "Heap.allocated", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "bool" []]] => fun (h : HeapV) (o : Option Int) => h.alloc o
  | "Heap.grows", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Heap" [],
      .tcons "bool" []]] => fun (h h' : HeapV) =>
    @decide (∀ o, h.alloc o = true → h'.alloc o = true) (Classical.propDecidable _)
  | "Heap.onlyModifies", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Heap" [],
      .tcons "arrow" [.tcons "Locs" [], .tcons "bool" []]]] =>
    fun (h h' : HeapV) (l : Option Int → Bool → Bool) =>
      @decide (∀ o, (l o false = false → h'.v o = h.v o) ∧
        (l o true = false → h'.next o = h.next o))
        (Classical.propDecidable _)
  | "Field.id", .tcons "arrow" [.tcons "Field" [.tcons "int" []], .tcons "FieldId" []] =>
    fun (_ : Unit) => false
  | "Field.id", .tcons "arrow" [.tcons "Field" [.tcons "Ref" []], .tcons "FieldId" []] =>
    fun (_ : Unit) => true
  | "Locs.mem", .tcons "arrow" [.tcons "Locs" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "FieldId" [], .tcons "bool" []]]] =>
    fun (l : Option Int → Bool → Bool) (o : Option Int) (k : Bool) => l o k
  | "Locs.at", .tcons "arrow" [.tcons "Ref" [], .tcons "arrow" [.tcons "FieldId" [],
      .tcons "Locs" []]] =>
    fun (p : Option Int) (j : Bool) (o : Option Int) (k : Bool) => decide (o = p ∧ k = j)
  | "Locs.object", .tcons "arrow" [.tcons "Ref" [], .tcons "Locs" []] =>
    fun (p : Option Int) (o : Option Int) (_ : Bool) => decide (o = p)
  | _, s => @default _ (SortDenote.inhabited carrier carrier_inhabited.inhabited s)


/-! ## The factory -/

/-- The names of the reference, tag and heap-API functions of the program. -/
private def apiNames : List String :=
  ["Null", "Obj", "Ref..isObj", "Ref.tag", "Box$Tag", "Locs.none", "Heap.read", "Heap.write",
    "Heap.allocated", "Heap.grows", "Heap.onlyModifies", "Field.id", "Locs.mem", "Locs.at",
    "Locs.object", "Box.v", "Box.next"]

/-- The functions of the factory have distinct names. -/
private theorem funcs_nodup : ((funcs apiNames).toList.map (·.name.name)).Nodup := by decide

/-- The modeled factory of the program's runs. -/
private noncomputable abbrev fac : Core.Expression.Factory := HeapModel.fac apiNames carrier opI rfl

/-- A Boolean value of the model holds exactly when its Boolean is `true`. -/
private theorem holds {b : Bool} :
    (some ⟨carrier, .bool, b⟩ : Option SemValue) = some (HasBool.ttVal (P := Core.Expression) fac)
      ↔ b = true :=
  holds_iff

/-! ## The laws -/

/-- The model satisfies the reference laws of a program whose composites are all `Box`. -/
private theorem refTag {Γ : UnorderedProgram} (hn : ∀ n ∈ refTagNames Γ, n ∈ "Bool.Not" :: apiNames)
    (hc : ∀ c ∈ Γ.composites, c.name = "Box") : RefTagModel Γ fac where
  declared n h := name_mem funcs_nodup (hn n h)
  tagsDistinct c hc' d hd hne := absurd ((hc c hc').trans (hc d hd).symm) hne
  nullNotObj := by
    api_eval
    rfl
  objIsObj a t ha ht := by
    obtain ⟨x, rfl⟩ := ofTy ha
    obtain ⟨y, rfl⟩ := ofTy ht
    api_eval
    rfl
  tagOfObj a t ha ht := by
    obtain ⟨x, rfl⟩ := ofTy ha
    obtain ⟨y, rfl⟩ := ofTy ht
    api_eval
    exact some_bool (@decide_eq_true _ (Classical.propDecidable _)
      (Subsingleton.elim (α := Unit) _ _))
  refCases o ho hf := by
    obtain ⟨x, rfl⟩ := ofTy ho
    have he : apiEval fac [("$o", ⟨carrier, _, x⟩)] (isObjT (apiVar "$o")) =
        some ⟨carrier, .bool, (show Option Int from x).isSome⟩ := by
      api_eval
      rfl
    have hx : (show Option Int from x) = none :=
      Option.not_isSome_iff_eq_none.mp (by simp [bool_inj (he.symm.trans hf)])
    api_eval
    exact some_bool (@decide_eq_true _ (Classical.propDecidable _) hx)


/-- A reference of the model. -/
private abbrev RefV := Option Int
/-- A location set of the model. -/
private abbrev LocsV := Option Int → Bool → Bool

/-- A value of the model at the sort of `t`. -/
private abbrev sv (t : LMonoTy) (x : SortDenote carrier (t.substTyVars fun _ => .bool)) :
    SemValue :=
  ⟨carrier, _, x⟩

/-- The binding of the variable `n` to the value `x` of the sort of `t`. -/
private abbrev bnd (n : String) (t : LMonoTy)
    (x : SortDenote carrier (t.substTyVars fun _ => .bool)) : String × SemValue :=
  (n, sv t x)

/-- `Heap.allocated(h, o)` is the allocation of `o` in `h`. -/
private theorem allocated_eval (x : HeapV) (y : RefV) :
    apiEval fac [bnd "$h" heapTy x, bnd "$o" refTy y] (allocatedT (apiVar "$h") (apiVar "$o")) =
      some ⟨carrier, .bool, x.alloc y⟩ := by
  api_eval
  rfl

/-- `Heap.grows(h, h')` holds when every reference allocated in `h` is allocated in `h'`. -/
private theorem grows_eval (x y : HeapV) :
    apiEval fac [bnd "$h" heapTy x, bnd "$h'" heapTy y] (growsT (apiVar "$h") (apiVar "$h'")) =
      some ⟨carrier, .bool,
        @decide (∀ o, x.alloc o = true → y.alloc o = true) (Classical.propDecidable _)⟩ := by
  api_eval
  rfl

/-- `Heap.onlyModifies(h, h', L)` holds when `h'` agrees with `h` on every field outside
`L`. -/
private theorem onlyMod_eval (a b : HeapV) (c : LocsV) :
    apiEval fac [bnd "$h" heapTy a, bnd "$h'" heapTy b, bnd "$L" locsTy c]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) =
    some ⟨carrier, .bool, @decide (∀ o, (c o false = false → b.v o = a.v o) ∧
      (c o true = false → b.next o = a.next o)) (Classical.propDecidable _)⟩ := by
  api_eval
  rfl

/-- `Locs.mem(L, o, k)` is the membership of `(o, k)` in `L`. -/
private theorem mem_eval (c : LocsV) (o : RefV) (k : Bool) :
    apiEval fac [bnd "$L" locsTy c, bnd "$o" refTy o, bnd "$k" fieldIdTy k]
      (locsMemT (apiVar "$L") (apiVar "$o") (apiVar "$k")) = some ⟨carrier, .bool, c o k⟩ := by
  api_eval
  rfl

/-- The field `Box.v`. -/
private abbrev fv : FieldRef := ⟨"Box", "v"⟩
/-- The field `Box.next`. -/
private abbrev fn : FieldRef := ⟨"Box", "next"⟩

/-- `Heap.read(h, o, Box.v)` is the value of `v` at `o` in `h`. -/
private theorem readV_eval (x : HeapV) (y : RefV) :
    apiEval fac [bnd "$h" heapTy x, bnd "$o" refTy y]
      (readT .int (apiVar "$h") (apiVar "$o") (fieldConst fv .int)) =
    some ⟨carrier, LMonoTy.int.substTyVars fun _ => .bool, x.v y⟩ := by
  api_eval
  rfl

/-- `Heap.read(h, o, Box.next)` is the value of `next` at `o` in `h`. -/
private theorem readN_eval (x : HeapV) (y : RefV) :
    apiEval fac [bnd "$h" heapTy x, bnd "$o" refTy y]
      (readT refTy (apiVar "$h") (apiVar "$o") (fieldConst fn refTy)) =
    some ⟨carrier, refTy.substTyVars fun _ => .bool, x.next y⟩ := by
  api_eval
  rfl

/-- `Heap.write(h, o, Box.v, w)` gives `v` the value `w` at `o`. -/
private theorem writeV_eval (x : HeapV) (y : RefV) (z : Int) :
    apiEval fac [bnd "$h" heapTy x, bnd "$o" refTy y, bnd "$w" .int z]
      (writeT .int (apiVar "$h") (apiVar "$o") (fieldConst fv .int) (apiVar "$w")) =
    some ⟨carrier, heapTy.substTyVars fun _ => .bool,
      ({ x with v := fun p => if p = y then z else x.v p } : HeapV)⟩ := by
  api_eval
  rfl

/-- `Heap.write(h, o, Box.next, w)` gives `next` the value `w` at `o`. -/
private theorem writeN_eval (x : HeapV) (y z : RefV) :
    apiEval fac [bnd "$h" heapTy x, bnd "$o" refTy y, bnd "$w" refTy z]
      (writeT refTy (apiVar "$h") (apiVar "$o") (fieldConst fn refTy) (apiVar "$w")) =
    some ⟨carrier, heapTy.substTyVars fun _ => .bool,
      ({ x with next := fun p => if p = y then z else x.next p } : HeapV)⟩ := by
  api_eval
  rfl

/-- `Locs.mem(L, o, Field.id(Box.v))` is the membership of `(o, false)` in `L`. -/
private theorem memV_eval (c : LocsV) (o : RefV) :
    apiEval fac [bnd "$L" locsTy c, bnd "$o" refTy o]
      (locsMemT (apiVar "$L") (apiVar "$o") (fieldIdT .int (fieldConst fv .int))) =
    some ⟨carrier, .bool, c o false⟩ := by
  api_eval
  rfl

/-- `Locs.mem(L, o, Field.id(Box.next))` is the membership of `(o, true)` in `L`. -/
private theorem memN_eval (c : LocsV) (o : RefV) :
    apiEval fac [bnd "$L" locsTy c, bnd "$o" refTy o]
      (locsMemT (apiVar "$L") (apiVar "$o") (fieldIdT refTy (fieldConst fn refTy))) =
    some ⟨carrier, .bool, c o true⟩ := by
  api_eval
  rfl

/-- The fields `Box.v : int` and `Box.next : Ref` that the model interprets. -/
private def ModelFields (Γ : UnorderedProgram) : Prop :=
  ∀ r d, (r, d) ∈ programFields Γ →
    (r = fv ∧ fieldMonoTy Γ d = .int) ∨ (r = fn ∧ fieldMonoTy Γ d = refTy)

/-- The model satisfies the heap laws of a program whose fields are among `Box.v : int` and
`Box.next : Ref`. -/
private theorem heapApi {Γ : UnorderedProgram}
    (hn : ∀ n ∈ heapApiNames Γ, n ∈ "Bool.Not" :: apiNames) (hf : ModelFields Γ) :
    HeapApiModel Γ fac where
  declared n h := name_mem funcs_nodup (hn n h)
  memNone o k ho hk := by
    obtain ⟨y, rfl⟩ := ofTy ho
    obtain ⟨z, rfl⟩ := ofTy hk
    api_eval
    rfl
  nullNotAllocated h hh := by
    obtain ⟨x, rfl⟩ := ofTy hh
    api_eval
    rfl
  grows h0 h1 hh0 hh1 := by
    obtain ⟨x, rfl⟩ := ofTy hh0
    obtain ⟨y, rfl⟩ := ofTy hh1
    refine ((iff_of_eq (congrArg (· = _) (grows_eval x y))).trans holds_iff).trans
      ((@decide_eq_true_iff _ (Classical.propDecidable _)).trans ?_)
    refine ⟨fun h o ho ha => ?_, fun h o ha => ?_⟩
    · obtain ⟨q, rfl⟩ := ofTy ho
      exact (allocated_eval y q).trans (holds_iff.mpr (h q (holds_iff.mp
        ((allocated_eval x q).symm.trans ha))))
    · exact holds_iff.mp ((allocated_eval y o).symm.trans (h (bnd "$o" refTy o).2 ⟨rfl, rfl⟩
        ((allocated_eval x o).trans (holds_iff.mpr ha))))
  onlyModifiesRefl h L hh hL := by
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨l, rfl⟩ := ofTy hL
    api_eval
    exact some_bool (@decide_eq_true _ (Classical.propDecidable _)
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩)
  onlyModifiesTrans h0 h1 h2 L M hh0 hh1 hh2 hL hM h01 h12 hsub := by
    obtain ⟨x0, rfl⟩ := ofTy hh0
    obtain ⟨x1, rfl⟩ := ofTy hh1
    obtain ⟨x2, rfl⟩ := ofTy hh2
    obtain ⟨l, rfl⟩ := ofTy hL
    obtain ⟨m, rfl⟩ := ofTy hM
    have h01' := @of_decide_eq_true _ (Classical.propDecidable _)
      (bool_inj ((onlyMod_eval x0 x1 l).symm.trans h01))
    have h12' := @of_decide_eq_true _ (Classical.propDecidable _)
      (bool_inj ((onlyMod_eval x1 x2 m).symm.trans h12))
    have hsub' (q : RefV) (k : Bool) (hq : (l : LocsV) q k = false) : (m : LocsV) q k = false :=
      Bool.eq_false_iff.mpr fun hm => by
        simp [bool_inj ((mem_eval l q k).symm.trans (hsub (bnd "$o" refTy q).2
          (bnd "$k" fieldIdTy k).2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
          ((mem_eval m q k).trans (holds_iff.mpr hm))))] at hq
    refine (onlyMod_eval x0 x2 l).trans
      (some_bool (@decide_eq_true _ (Classical.propDecidable _)
        fun q => ⟨fun hq => ?_, fun hq => ?_⟩))
    · exact ((h12' q).1 (hsub' q false hq)).trans ((h01' q).1 hq)
    · exact ((h12' q).2 (hsub' q true hq)).trans ((h01' q).2 hq)
  memAt p j o k hp hj ho hk := by
    obtain ⟨yp, rfl⟩ := ofTy hp
    obtain ⟨yj, rfl⟩ := ofTy hj
    obtain ⟨yo, rfl⟩ := ofTy ho
    obtain ⟨yk, rfl⟩ := ofTy hk
    change RefV at yp yo
    change Bool at yj yk
    have e1 : apiEval fac [bnd "$p" refTy yp, bnd "$j" fieldIdTy yj, bnd "$o" refTy yo,
        bnd "$k" fieldIdTy yk]
        (locsMemT (locsAtT (apiVar "$p") (apiVar "$j")) (apiVar "$o") (apiVar "$k")) =
        some ⟨carrier, .bool, decide (yo = yp ∧ yk = yj)⟩ := by
      api_eval
      rfl
    have e2 : apiEval fac [bnd "$p" refTy yp, bnd "$o" refTy yo]
        (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")) =
        some ⟨carrier, .bool, @decide (yo = yp) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    have e3 : apiEval fac [bnd "$j" fieldIdTy yj, bnd "$k" fieldIdTy yk]
        (.eq Core.coreLoc (apiVar "$k") (apiVar "$j")) =
        some ⟨carrier, .bool, @decide (yk = yj) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    simp only [apiHolds, e1, e2, e3]
    rw [holds, holds, holds]
    simp only [decide_eq_true_eq]
  memObject p o k hp ho hk := by
    obtain ⟨yp, rfl⟩ := ofTy hp
    obtain ⟨yo, rfl⟩ := ofTy ho
    obtain ⟨yk, rfl⟩ := ofTy hk
    change RefV at yp yo
    have e1 : apiEval fac [bnd "$p" refTy yp, bnd "$o" refTy yo, bnd "$k" fieldIdTy yk]
        (locsMemT (locsObjectT (apiVar "$p")) (apiVar "$o") (apiVar "$k")) =
        some ⟨carrier, .bool, decide (yo = yp)⟩ := by
      api_eval
      rfl
    have e2 : apiEval fac [bnd "$p" refTy yp, bnd "$o" refTy yo]
        (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")) =
        some ⟨carrier, .bool, @decide (yo = yp) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    simp only [apiHolds, e1, e2]
    rw [holds, holds]
    simp only [decide_eq_true_eq]
  fieldIdsDistinct r d hrd r' d' hrd' hne := by
    rcases hf r d hrd with ⟨rfl, hft⟩ | ⟨rfl, hft⟩ <;>
      rcases hf r' d' hrd' with ⟨rfl, hft'⟩ | ⟨rfl, hft'⟩
    all_goals first | exact absurd rfl hne | rw [hft, hft']
    all_goals api_eval
    all_goals exact some_bool (@decide_eq_false _ (Classical.propDecidable _) nofun)
  frame r d hrd h0 h1 L o hh0 hh1 hL ho hmod hnot := by
    obtain ⟨x0, rfl⟩ := ofTy hh0
    obtain ⟨x1, rfl⟩ := ofTy hh1
    obtain ⟨l, rfl⟩ := ofTy hL
    obtain ⟨y, rfl⟩ := ofTy ho
    have hm := @of_decide_eq_true _ (Classical.propDecidable _)
      (bool_inj ((onlyMod_eval x0 x1 l).symm.trans hmod))
    rcases hf r d hrd with ⟨rfl, hft⟩ | ⟨rfl, hft⟩ <;> rw [hft] at hnot ⊢
    · rw [readV_eval x1 y, readV_eval x0 y, (hm y).1 (bool_inj ((memV_eval l y).symm.trans hnot))]
    · rw [readN_eval x1 y, readN_eval x0 y, (hm y).2 (bool_inj ((memN_eval l y).symm.trans hnot))]
  readWriteSame r d hrd h o w h' hh ho hw hwr := by
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    rcases hf r d hrd with ⟨rfl, hft⟩ | ⟨rfl, hft⟩ <;> rw [hft] at hw hwr ⊢ <;>
      obtain ⟨z, rfl⟩ := ofTy hw
    · cases (writeV_eval x y z).symm.trans hwr
      exact (readV_eval _ y).trans (congrArg (fun v => (some ⟨carrier, _, v⟩ : Option SemValue))
        (ite_eq_left rfl))
    · cases (writeN_eval x y z).symm.trans hwr
      exact (readN_eval _ y).trans (congrArg (fun v => (some ⟨carrier, _, v⟩ : Option SemValue))
        (ite_eq_left rfl))
  writeOnlyModifies r d hrd h o w h' hh ho hw hwr := by
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    change RefV at y
    rcases hf r d hrd with ⟨rfl, hft⟩ | ⟨rfl, hft⟩ <;> rw [hft] at hw hwr ⊢ <;>
      obtain ⟨z, rfl⟩ := ofTy hw
    · cases (writeV_eval x y z).symm.trans hwr
      api_eval
      refine some_bool (@decide_eq_true _ (Classical.propDecidable _)
        fun p => ⟨fun hp => ?_, fun _ => rfl⟩)
      have hp' : decide (p = y ∧ false = false) = false := hp
      exact ite_eq_right fun h => by simp [h] at hp'
    · cases (writeN_eval x y z).symm.trans hwr
      api_eval
      refine some_bool (@decide_eq_true _ (Classical.propDecidable _)
        fun p => ⟨fun _ => rfl, fun hp => ?_⟩)
      have hp' : decide (p = y ∧ true = true) = false := hp
      exact ite_eq_right fun h => by simp [h] at hp'
  writeKeepsAllocated r d hrd h o w h' p hh ho hw hp hwr := by
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    obtain ⟨q, rfl⟩ := ofTy hp
    rcases hf r d hrd with ⟨rfl, hft⟩ | ⟨rfl, hft⟩ <;> rw [hft] at hw hwr <;>
      obtain ⟨z, rfl⟩ := ofTy hw
    · cases (writeV_eval x y z).symm.trans hwr
      exact (allocated_eval _ q).trans (allocated_eval x q).symm
    · cases (writeN_eval x y z).symm.trans hwr
      exact (allocated_eval _ q).trans (allocated_eval x q).symm

/-! ## Allocation -/

/-- Every reference has the tag of `Box`: the model has one tag. -/
private theorem tag_box (o : SemValue) (ho : IsOfTy fac o refTy) :
    apiHolds fac [("$o", o)] (.eq Core.coreLoc (tagOfT (apiVar "$o")) (tagConst "Box")) := by
  obtain ⟨y, rfl⟩ := ofTy ho
  api_eval
  exact some_bool (@decide_eq_true _ (Classical.propDecidable _)
    (Subsingleton.elim (α := Unit) _ _))

/-- `Null` is `Null`: the null reference is a safe reference. -/
private theorem null_safe (h : SemValue) : SafeRef fac h (sv refTy none) := fun _ => .inl (by
  api_eval
  exact some_bool (@decide_eq_true _ (Classical.propDecidable _) rfl))

/-- In every heap of the model, `new Box` can allocate `Obj(n, Box$Tag)` for the counter `n`:
the successor heap only increments the counter. -/
theorem newObj_model (h : HeapV) :
    NewObj fac (sv heapTy h) "Box" (sv refTy (some (h.count : Int)))
      (sv heapTy { h with count := h.count + 1 }) := by
  refine ⟨(allocated_eval _ _).trans (some_bool (by simp [HeapV.alloc])),
    (allocated_eval _ _).trans (some_bool (by simp [HeapV.alloc, Int.lt_add_one_iff])),
    tag_box _ ⟨rfl, rfl⟩,
    fun o ho ha => ?_, ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := ofTy ho
    have hq := bool_inj ((allocated_eval _ q).symm.trans ha)
    rcases q with _ | a
    · cases hq
    · simp only [HeapV.alloc, decide_eq_true_eq] at hq
      rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp (by simpa using hq.2)) with hlt | rfl
      · exact .inl ((allocated_eval _ _).trans (some_bool (by simp [HeapV.alloc, hq.1, hlt])))
      · exact .inr rfl
  · refine (grows_eval _ _).trans (some_bool (@decide_eq_true _ (Classical.propDecidable _) ?_))
    rintro (_ | a) ha
    · cases ha
    · simp only [HeapV.alloc, decide_eq_true_eq] at ha ⊢
      omega
  · api_eval
    exact some_bool (@decide_eq_true _ (Classical.propDecidable _)
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩)

/-! ## The program -/

/-- A body of one block, `b0`, running `cmds` and returning. -/
private def oneBlock (cmds : List IRCmd) : Body :=
  { cfg := { entry := "b0", blocks := [("b0", { cmds, transfer := .finish .empty })] },
    handlers := [] }

/-- The variable `n`. -/
private abbrev var (n : String) : Core.Expression.Ident := ⟨n, ()⟩

/-- The body of `main`: it declares `x : Box`, `y : int` and `z : Box`, then runs
`x := new Box`, `y := x#v` and `z := x#next`. -/
private def allocBody : Body :=
  oneBlock [.cmd (.init (var "x") (.forAll [] (tcon "Box")) .nondet .empty),
    .cmd (.init (var "y") (.forAll [] .int) .nondet .empty),
    .cmd (.init (var "z") (.forAll [] (tcon "Box")) .nondet .empty),
    .new (var "x") "Box" .empty,
    .readField (var "y") (mkFvar "x") fv .empty,
    .readField (var "z") (mkFvar "x") fn .empty]

/-- The program: the composite `Box` with the fields `v : int` and `next : Box`, and the
procedure `main`. -/
private def boxProg : UnorderedProgram :=
  { composites := [
      { name := "Box", extending := [],
        fields := [{ name := "v", ty := .forAll [] .int },
          { name := "next", ty := .forAll [] (tcon "Box") }] }],
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none, body := some allocBody }] }

/-- The program context of the runs. -/
private abbrev Γ₀ : UnorderedProgram := (Program.unordered boxProg).ctx

/-- The frame of a run of `main`. -/
private def allocFrame : Frame := ⟨allocBody, none, [], [], []⟩

/-- The heap the runs start from: nothing is allocated, every `v` is 0 and every `next` is
`Null`. -/
private def heap₀ : HeapV := ⟨0, fun _ => 0, fun _ => none⟩

/-- The initial environment: only `$entryHeap` is bound, to `heap₀`, and the factory is the
model's. -/
private noncomputable def env₀ : Imperative.Env Core.Expression :=
  ⟨fun x => if x = entryHeapVar then some (sv heapTy heap₀) else none, fac⟩

/-- The type `int` reads as itself. -/
private theorem eraseMono_int : eraseMono Γ₀ .int = .int := by
  simp [eraseMono, eraseRefs, eraseRefsList, constrainedValueTy, constrainedBase, isRefName,
    UnorderedProgram.findComposite?, boxProg, Program.ctx, LMonoTy.int]

/-- The composite type `Box` reads as `Ref`. -/
private theorem eraseMono_box : eraseMono Γ₀ (tcon "Box") = refTy := by
  simp [eraseMono, eraseRefs, constrainedValueTy, constrainedBase, isRefName,
    UnorderedProgram.findComposite?, boxProg, Program.ctx, refTy, tcon]

/-- A variable declared `int` holds an integer. -/
private theorem eraseTy_int : eraseTy Γ₀ (.forAll [] .int) = .forAll [] .int :=
  congrArg _ eraseMono_int

/-- A variable declared `Box` holds a reference. -/
private theorem eraseTy_box : eraseTy Γ₀ (.forAll [] (tcon "Box")) = .forAll [] refTy :=
  congrArg _ eraseMono_box

/-- The field `v` of `Box` has type `int`. -/
private theorem fieldMonoTy_v : fieldMonoTy Γ₀ ⟨"v", .forAll [] .int⟩ = .int := eraseMono_int

/-- The field `next` of `Box` has type `Ref`. -/
private theorem fieldMonoTy_next : fieldMonoTy Γ₀ ⟨"next", .forAll [] (tcon "Box")⟩ = refTy :=
  eraseMono_box

/-- The initial-environment well-formedness `CortexInitEnvWF` holds for `main`. -/
theorem initEnvWF_alloc (params : Core.Logic.InitEnvWFParams) :
    CortexInitEnvWF Γ₀ params allocFrame env₀ where
  toWellFormedSemanticEval := Core.coreEvaluator_WellFormedSemanticEval fac
    (get_funcs funcs_nodup (g := (boolNotFunc (T := Core.CoreLParams)).func) (by simp [funcs]))
  storeWellDefined x v h := by
    simp only [env₀] at h
    split at h
    · cases h
      rfl
    · cases h
  refTag := refTag (by decide) (by decide)
  heapApi := heapApi (by decide) fun r d h => by
    simp only [programFields, boxProg, Program.ctx, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, fieldMonoTy_v⟩
    · exact .inr ⟨rfl, fieldMonoTy_next⟩
  procsWF p hp b hb := by
    simp only [boxProg, Program.ctx, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    cases hb
    exact ⟨.nil, .nil, rfl⟩
  entryHandlers := rfl
  entryReadsDefined x hx hnd := by
    simp_all [allocFrame, allocBody, oneBlock, Body.used, Body.declared, IRCmd.declared,
      IRCmd.exprs, IRCmd.updated, HasFvars.getFvars, LExpr.LExpr.getVars, mkFvar]
  globalsTyped xt hx := by simp [boxProg, Program.ctx] at hx
  paramsTyped p hp _ xt hx := by
    simp only [boxProg, Program.ctx, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    simp at hx
  entryHeap := ⟨sv heapTy heap₀, by simp [env₀], ⟨rfl, rfl⟩,
    fun o ho _ => ⟨_, List.mem_singleton_self _, tag_box o ho⟩⟩
  reservedFresh n hn h := by
    simp [env₀, hn] at h

/-- The runs of `main` from the initial environment start with safe references: the store binds
only the heap, the field `v` holds integers and the field `next` holds `Null`, and no expression
builds a reference. -/
theorem safeStart_alloc : SafeStart (.unordered boxProg) allocFrame env₀ where
  storeSafe x v hx h := by simp [env₀, hx] at h
  heapClosed r d hd o w ho hr := by
    have he : entryHeap env₀.factory env₀.store = sv heapTy heap₀ := by
      simp [entryHeap, env₀, entryHeapVar]
    rw [he] at hr ⊢
    obtain ⟨y, rfl⟩ := ofTy ho
    have h := findField?_mem hd
    simp only [programFields, boxProg, Program.ctx, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [fieldMonoTy_v] at hr
      cases (readV_eval heap₀ y).symm.trans hr
      exact safeRef_of_isOfTy (t := .int) ⟨rfl, rfl⟩ (by decide)
    · rw [fieldMonoTy_next] at hr
      cases (readN_eval heap₀ y).symm.trans hr
      exact null_safe _
  noRefOps := ⟨rfl, rfl⟩

/-! ## The run -/

/-- The store after `main` declares `x`, `y` and `z` with the values `Null`, 0 and `Null`. -/
private noncomputable def σ₃ : Store :=
  ((env₀.store.update (var "x") (sv refTy none)).update (var "y") (sv .int (0 : Int))).update
    (var "z") (sv refTy none)

/-- The heap after `x := new Box`: the counter is 1. -/
private def heap₁ : HeapV := { heap₀ with count := 1 }

/-- The store at the end of `main`: `x` is the new object, `y` its `v` and `z` its `next`. -/
private noncomputable def σ₆ : Store :=
  ((σ₃.update (var "x") (sv refTy (some 0))).update (var "y") (sv .int (0 : Int))).update
    (var "z") (sv refTy none)

/-- A step that emits nothing, followed by a run that emits nothing, is a run that emits
nothing. -/
private theorem step_nil {x y z : CConfig} (h : StepCortex Γ₀ (EvalIRCmd Γ₀) x [] y)
    (t : ReflTransTrace (StepCortex Γ₀ (EvalIRCmd Γ₀)) y [] z) :
    ReflTransTrace (StepCortex Γ₀ (EvalIRCmd Γ₀)) x [] z :=
  .step _ _ _ _ _ h t

/-- From the initial environment, the entry body of `main` runs to its end, emitting no
event, and ends with `x` the object `Obj(0, Box$Tag)` allocated by `new Box`, `y` the value
0 of its field `v` and `z` the value `Null` of its field `next`. -/
theorem alloc_run :
    (EventLang.cortex (.unordered boxProg)).traceStar
      ((EventLang.cortex (.unordered boxProg)).stmtCfg allocFrame env₀) []
      (.terminal { env₀ with store := σ₆ }) ∧
    σ₆ (var "x") = some (sv refTy (some 0)) ∧ σ₆ (var "y") = some (sv .int (0 : Int)) ∧
    σ₆ (var "z") = some (sv refTy none) := by
  have hwf := Core.coreEvaluator_WellFormedSemanticEvalVar fac
  refine ⟨?_, by simp [σ₆, SemanticStore.update], by simp [σ₆, SemanticStore.update],
    by simp [σ₆, SemanticStore.update]⟩
  have he : entryHeap env₀.factory env₀.store = sv heapTy heap₀ := by
    simp [entryHeap, env₀, entryHeapVar]
  simp only [EventLang.cortex, Strata.Logic.EventLang.traceStar, he]
  refine step_nil (StepCortex.fetch rfl) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.base (evs := [])
    (.eval_init_unconstrained
      (InitState.of_update (v := sv refTy none) (by simp [env₀, entryHeapVar]))
      (by rw [eraseTy_box]; exact ⟨rfl, rfl⟩) hwf)
    (safe_writes_update (v := sv refTy none) (null_safe _)))) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.base (evs := [])
    (.eval_init_unconstrained (InitState.of_update (v := sv .int (0 : Int))
      (by simp [env₀, entryHeapVar, SemanticStore.update]))
      (by rw [eraseTy_int]; exact ⟨rfl, rfl⟩) hwf)
    (safe_writes_update (safeRef_of_isOfTy (t := .int) ⟨rfl, rfl⟩ (by decide))))) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.base (evs := [])
    (.eval_init_unconstrained (InitState.of_update (v := sv refTy none)
      (by simp [env₀, entryHeapVar, SemanticStore.update]))
      (by rw [eraseTy_box]; exact ⟨rfl, rfl⟩) hwf)
    (safe_writes_update (v := sv refTy none) (null_safe _)))) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.new rfl (newObj_model heap₀)
    ⟨sv refTy none, .forAll [] refTy, by simp [SemanticStore.update], ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    (UpdateState.of_update (old := sv refTy none) (by simp [SemanticStore.update])))) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.readField
    (Core.eval_fvar fac (by simp [SemanticStore.update, heap₀]) rfl)
    ((allocated_eval heap₁ (some 0)).trans (some_bool rfl)) rfl
    ((congrArg (fun t => apiEval fac _ (readT t _ _ (fieldConst fv t))) fieldMonoTy_v).trans
      (readV_eval heap₁ (some 0)))
    (UpdateState.of_update (old := sv .int (0 : Int)) (by simp [SemanticStore.update])))) ?_
  refine step_nil (StepCortex.cmd_normal (EvalIRCmd.readField
    (Core.eval_fvar fac (by simp [SemanticStore.update, heap₀]) rfl)
    ((allocated_eval heap₁ (some 0)).trans (some_bool rfl)) rfl
    ((congrArg (fun t => apiEval fac _ (readT t _ _ (fieldConst fn t))) fieldMonoTy_next).trans
      (readN_eval heap₁ (some 0)))
    (UpdateState.of_update (old := sv refTy none) (by simp [SemanticStore.update])))) ?_
  exact step_nil StepCortex.finish (step_nil StepCortex.close (.refl _))

/-! ## No vacuous premise for the object commands -/

/-- Allocation is possible in every heap of the model: for every heap `h`, `new Box` has a
reference and a successor heap that the postconditions of `Heap.new` allow. -/
theorem newObj_exists (h : SemValue) (hh : IsOfTy fac h heapTy) :
    ∃ v h', NewObj fac h "Box" v h' := by
  obtain ⟨x, rfl⟩ := ofTy hh
  exact ⟨_, _, newObj_model x⟩

/-- The premise `CortexInitEnvWF` of the Cortex trace-inclusion theorems holds for a program
that allocates an object and reads its fields, and from that environment the run reaches
the end of the program, through steps of `new` and `readField`. -/
theorem alloc_nonvacuous (params : Core.Logic.InitEnvWFParams) :
    ∃ ρ ρ', (EventLang.cortex (.unordered boxProg)).initEnvWF params allocFrame ρ ∧
      (EventLang.cortex (.unordered boxProg)).traceStar
        ((EventLang.cortex (.unordered boxProg)).stmtCfg allocFrame ρ) []
        ((EventLang.cortex (.unordered boxProg)).terminalCfg ρ') :=
  ⟨env₀, _, initEnvWF_alloc params, alloc_run.1⟩

/-! ## A program that builds a reference is refused -/

/-- `boxProg` with a `main` that writes the reference `Obj(5, Box$Tag)`, which no `new`
allocated, to `x`. -/
private def objProg : UnorderedProgram :=
  { boxProg with
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none
        body := some (oneBlock [
          .cmd (.init (var "x") (.forAll [] (tcon "Box")) .nondet .empty),
          .cmd (.set (var "x") (.det (objT (intLit 5) (tagConst "Box"))) .empty)]) }] }

/-- The check that source expressions build no reference refuses `objProg`, so no run of it
starts with safe references. -/
theorem objProg_refused (fr : Frame) (ρ : Imperative.Env Core.Expression) :
    objProg.noRefOps = false ∧ ¬ SafeStart (.unordered objProg) fr ρ :=
  have h : objProg.noRefOps = false := rfl
  ⟨h, fun hs => Bool.false_ne_true (h.symm.trans hs.noRefOps.1)⟩

/-- The body of a `main` that writes `mkRef(5)` to `x`, the operator `mkRef` annotated
`int → Box`. -/
private def mkRefBody : Body :=
  oneBlock [.cmd (.init (var "x") (.forAll [] (tcon "Box")) .nondet .empty),
    .cmd (.set (var "x") (.det (apiCall "mkRef" [.int] (tcon "Box") [intLit 5])) .empty)]

/-- `boxProg` with the `main` of `mkRefBody`. -/
private def mkRefProg : UnorderedProgram :=
  { boxProg with
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none, body := some mkRefBody }] }

/-- The type `Box` has no type variable. -/
private theorem box_freeVars : (tcon "Box").freeVars = [] := rfl

/-- `Box` reads as `Ref` in `mkRefProg`. -/
private theorem mkRef_eraseBox : eraseMono mkRefProg (tcon "Box") = refTy := by
  simp [eraseMono, eraseRefs, constrainedValueTy, constrainedBase, isRefName,
    UnorderedProgram.findComposite?, mkRefProg, boxProg, refTy, tcon]

/-- An operator annotated with a result type that erases to `Ref` builds a reference: the
check refuses `mkRefProg`. -/
theorem mkRefProg_refused : mkRefProg.noRefOps = false := by
  have hp : mkRefProg.noRefOps = (mkRefBody.noRefOps mkRefProg && true) := rfl
  have hd : (LMonoTy.arrow .int (tcon "Box")).destructArrow = [.int, tcon "Box"] := rfl
  simp (config := { decide := true }) [hp, mkRefBody, Body.noRefOps, oneBlock, IRCmd.exprs,
    exprNoRefOps, apiCall, mkApp, intLit, noRefOp, notRefTy, hd, box_freeVars, mkRef_eraseBox]

/-- The check reads only the annotation: it refuses `Obj`, an operator annotated `a → a` and one
annotated `int → Box`, and accepts an operator annotated `int → int`, whatever its declaration,
and one without an annotation, which has no value. -/
theorem noRefOp_annotation :
    noRefOp mkRefProg "Obj" none = false ∧
    noRefOp mkRefProg "f" (some (.arrow (.ftvar "a") (.ftvar "a"))) = false ∧
    noRefOp mkRefProg "mkRef" (some (.arrow .int (tcon "Box"))) = false ∧
    noRefOp mkRefProg "mkRef" (some (.arrow .int .int)) = true ∧
    noRefOp mkRefProg "mkRef" none = true := by
  have hi : eraseMono mkRefProg .int = .int := by
    simp [eraseMono, eraseRefs, eraseRefsList, constrainedValueTy, constrainedBase, isRefName,
      UnorderedProgram.findComposite?, mkRefProg, boxProg, LMonoTy.int]
  have hb : (LMonoTy.arrow .int (tcon "Box")).destructArrow = [.int, tcon "Box"] := rfl
  have hd : (LMonoTy.arrow .int .int).destructArrow = [.int, .int] := rfl
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;>
    simp (config := { decide := true }) [noRefOp, notRefTy, hb, hd, box_freeVars,
      mkRef_eraseBox, hi, LMonoTy.freeVars, LMonoTys.freeVars, refTy]

/-! ## A program over a map is accepted -/

/-- The type `Map int int`. -/
private def mapII : LMonoTy := .tcons "Map" [.int, .int]

/-- The body of a `main` that updates the map `m` at `1` and reads it back, with the operators
`update` and `select` annotated at `Map int int`, as the front ends annotate them. -/
private def mapBody : Body :=
  oneBlock [.cmd (.init (var "m") (.forAll [] mapII) .nondet .empty),
    .cmd (.set (var "m") (.det (apiCall "update" [mapII, .int, .int] mapII
      [mkFvar "m", intLit 1, intLit 2])) .empty),
    .cmd (.init (var "y") (.forAll [] .int)
      (.det (apiCall "select" [mapII, .int] .int [mkFvar "m", intLit 1])) .empty)]

/-- `boxProg` with the `main` of `mapBody`. -/
private def mapProg : UnorderedProgram :=
  { boxProg with
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none, body := some mapBody }] }

/-- The check accepts `mapProg`: `update` and `select`, polymorphic in Core's factory, are
annotated with ground result types that are no reference. -/
theorem mapProg_noRefOps : mapProg.noRefOps = true := by
  have hp : mapProg.noRefOps = (mapBody.noRefOps mapProg && true) := rfl
  have hm : eraseMono mapProg mapII = mapII := by
    simp [eraseMono, eraseRefs, eraseRefsList, constrainedValueTy, constrainedValueTyList,
      constrainedBase, isRefName, UnorderedProgram.findComposite?, mapProg, boxProg, mapII,
      arrayElem?, LMonoTy.int]
  have hi : eraseMono mapProg .int = .int := by
    simp [eraseMono, eraseRefs, eraseRefsList, constrainedValueTy, constrainedBase, isRefName,
      UnorderedProgram.findComposite?, mapProg, boxProg, LMonoTy.int]
  have hu : (mapII.arrow (.arrow .int (.arrow .int mapII))).destructArrow =
      [mapII, .int, .int, mapII] := rfl
  have hs : (mapII.arrow (.arrow .int .int)).destructArrow = [mapII, .int, .int] := rfl
  have hf : mapII.freeVars = [] := rfl
  simp (config := { decide := true }) [hp, mapBody, Body.noRefOps, oneBlock, IRCmd.exprs,
    exprNoRefOps, apiCall, mkApp, mkFvar, intLit, noRefOp, notRefTy, hu, hs, hf, hm, hi,
    LMonoTy.freeVars, LMonoTys.freeVars]

end Cortex.Sem.AllocModelExamples
