/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Cortex.LangDef
import Strata.Languages.Cortex.HeapProps
import all Strata.Languages.Cortex.Ordering
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Cortex.Semantics
import all Strata.Languages.Cortex.LangDef
import all Strata.Languages.Cortex.Module
import all Strata.Languages.Cortex.AST
import all StrataTest.Languages.Cortex.HeapModelHelpers

/-! # The initial-environment well-formedness of Cortex is satisfiable

`CortexInitEnvWF` is the premise of every Cortex trace-inclusion theorem. This file builds a
factory with a consistent model of the references and of the heap API, and proves that the
premise holds for two small programs: one without composites, an `int` local and a call, in
the domain of `Ordering.order`, and one with a composite of one `int` field.

The model: a reference is `none` (`Null`) or `some a` (`Obj(a, t)`), every tag is the unit
value, a heap maps each reference to the value of its one `int` field, no reference is ever
allocated, and a location set is a set of references. The runs start from the heap that maps
every reference to 0, bound to `$entryHeap`.

## Key results

- `initEnvWF_noComposites`, `initEnvWF_box`: the premise holds for the two programs.
- `noComposites_order`: the first program is in the domain of `Ordering.order`.
- `initEnvWF_without_composites_satisfiable`, `initEnvWF_ordered_satisfiable`: the premise is
  not refuted by the absence of composites, nor on the programs `Ordering.order` accepts.
-/

namespace Cortex.Sem.InitEnvWFExamples

open Imperative Lambda HeapModel

/-! ## The model -/

/-- The carriers of the sorts the model interprets: references, heaps and location sets. -/
private def carrier : String → List LSort → Type
  | "Ref", [] => Option Int
  | "Heap", [] => Option Int → Int
  | "Locs", [] => Option Int → Bool
  | _, _ => Unit

private instance carrier_inhabited : TyConstrInterp.AllInhabited carrier where
  inhabited name args := by
    unfold carrier
    split
    · exact ⟨none⟩
    · exact ⟨fun _ => 0⟩
    · exact ⟨fun _ => false⟩
    · exact ⟨()⟩

/-- The interpretation of the operators. -/
private noncomputable def opI : (name : String) → (s : LSort) → SortDenote carrier s
  | "Bool.Not", .tcons "arrow" [.tcons "bool" [], .tcons "bool" []] => fun (b : Bool) => !b
  | "Null", .tcons "Ref" [] => (none : Option Int)
  | "Obj", .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "Tag" [], .tcons "Ref" []]] =>
    fun (a : Int) (_ : Unit) => (some a : Option Int)
  | "Ref..isObj", .tcons "arrow" [.tcons "Ref" [], .tcons "bool" []] =>
    fun (o : Option Int) => o.isSome
  | "Ref.tag", .tcons "arrow" [.tcons "Ref" [], .tcons "Tag" []] => fun (_ : Option Int) => ()
  | "Locs.none", .tcons "Locs" [] => fun (_ : Option Int) => false
  | "Heap.read", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "int" []], .tcons "int" []]]] =>
    fun (h : Option Int → Int) (o : Option Int) (_ : Unit) => h o
  | "Heap.write", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "Field" [.tcons "int" []], .tcons "arrow" [.tcons "int" [],
      .tcons "Heap" []]]]] =>
    fun (h : Option Int → Int) (o : Option Int) (_ : Unit) (w : Int) (p : Option Int) =>
      if p = o then w else h p
  | "Heap.allocated", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "bool" []]] => fun (_ : Option Int → Int) (_ : Option Int) => false
  | "Heap.grows", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Heap" [],
      .tcons "bool" []]] => fun (_ _ : Option Int → Int) => true
  | "Heap.onlyModifies", .tcons "arrow" [.tcons "Heap" [], .tcons "arrow" [.tcons "Heap" [],
      .tcons "arrow" [.tcons "Locs" [], .tcons "bool" []]]] =>
    fun (h h' : Option Int → Int) (l : Option Int → Bool) =>
      @decide (∀ o, l o = false → h' o = h o) (Classical.propDecidable _)
  | "Locs.mem", .tcons "arrow" [.tcons "Locs" [], .tcons "arrow" [.tcons "Ref" [],
      .tcons "arrow" [.tcons "FieldId" [], .tcons "bool" []]]] =>
    fun (l : Option Int → Bool) (o : Option Int) (_ : Unit) => l o
  | "Locs.at", .tcons "arrow" [.tcons "Ref" [], .tcons "arrow" [.tcons "FieldId" [],
      .tcons "Locs" []]] => fun (p : Option Int) (_ : Unit) (o : Option Int) => decide (o = p)
  | "Locs.object", .tcons "arrow" [.tcons "Ref" [], .tcons "Locs" []] =>
    fun (p : Option Int) (o : Option Int) => decide (o = p)
  | _, s => @default _ (SortDenote.inhabited carrier carrier_inhabited.inhabited s)

/-! ## The factory -/

/-- The names of the reference, tag and heap-API functions of both programs. -/
private def apiNames : List String :=
  ["Null", "Obj", "Ref..isObj", "Ref.tag", "Box$Tag", "Locs.none", "Heap.read", "Heap.write",
    "Heap.allocated", "Heap.grows", "Heap.onlyModifies", "Field.id", "Locs.mem", "Locs.at",
    "Locs.object", "Box.v"]

/-- The functions of the factory have distinct names. -/
private theorem funcs_nodup : ((funcs apiNames).toList.map (·.name.name)).Nodup := by decide

/-- The modeled factory of the two programs' runs. -/
private noncomputable abbrev fac : Core.Expression.Factory := HeapModel.fac apiNames carrier opI rfl

/-- A Boolean value of the model holds exactly when its Boolean is `true`. -/
private theorem holds {b : Bool} :
    (some ⟨carrier, .bool, b⟩ : Option SemValue) = some (HasBool.ttVal (P := Core.Expression) fac)
      ↔ b = true :=
  holds_iff

/-- No reference is allocated in any heap of the model. -/
private theorem allocated_fails {h o : SemValue} (hh : IsOfTy fac h heapTy)
    (ho : IsOfTy fac o refTy) :
    apiFails fac [("$h", h), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) := by
  obtain ⟨x, rfl⟩ := ofTy hh
  obtain ⟨y, rfl⟩ := ofTy ho
  api_eval
  rfl

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


/-- A heap of the model. -/
private abbrev HeapV := Option Int → Int
/-- A reference of the model. -/
private abbrev RefV := Option Int
/-- A location set of the model. -/
private abbrev LocsV := Option Int → Bool
/-- A field identity of the model. -/
private abbrev FidV := Unit

/-- `Heap.onlyModifies(h, h', L)` holds when `h'` agrees with `h` outside `L`. -/
private theorem onlyMod_eval (a b : HeapV) (c : LocsV) :
    apiEval fac [("$h", ⟨carrier, heapTy.substTyVars fun _ => .bool, a⟩),
        ("$h'", ⟨carrier, heapTy.substTyVars fun _ => .bool, b⟩),
        ("$L", ⟨carrier, locsTy.substTyVars fun _ => .bool, c⟩)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) =
    some ⟨carrier, .bool,
      @decide (∀ o, c o = false → b o = a o) (Classical.propDecidable _)⟩ := by
  api_eval
  rfl

/-- `Locs.mem(L, o, k)` is the membership of `o` in `L`. -/
private theorem mem_eval (c : LocsV) (o : RefV) (k : FidV) :
    apiEval fac [("$L", ⟨carrier, locsTy.substTyVars fun _ => .bool, c⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, o⟩),
        ("$k", ⟨carrier, fieldIdTy.substTyVars fun _ => .bool, k⟩)]
      (locsMemT (apiVar "$L") (apiVar "$o") (apiVar "$k")) =
    some ⟨carrier, .bool, c o⟩ := by
  api_eval
  rfl

/-- `Heap.read(h, o, Box.v)` is the value `h` gives `o`. -/
private theorem read_eval (x : HeapV) (y : RefV) :
    apiEval fac [("$h", ⟨carrier, heapTy.substTyVars fun _ => .bool, x⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, y⟩)]
      (readT .int (apiVar "$h") (apiVar "$o") (fieldConst ⟨"Box", "v"⟩ .int)) =
    some ⟨carrier, LMonoTy.int.substTyVars fun _ => .bool, x y⟩ := by
  api_eval
  rfl

/-- `Heap.write(h, o, Box.v, w)` gives `o` the value `w`. -/
private theorem write_eval (x : HeapV) (y : RefV) (z : Int) :
    apiEval fac [("$h", ⟨carrier, heapTy.substTyVars fun _ => .bool, x⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, y⟩),
        ("$w", ⟨carrier, LMonoTy.int.substTyVars fun _ => .bool, z⟩)]
      (writeT .int (apiVar "$h") (apiVar "$o") (fieldConst ⟨"Box", "v"⟩ .int) (apiVar "$w")) =
    some ⟨carrier, heapTy.substTyVars fun _ => .bool,
      (fun p => if p = y then z else x p : HeapV)⟩ := by
  api_eval
  rfl

/-- `Heap.allocated(h, o)` is `false`. -/
private theorem allocated_eval (x : HeapV) (y : RefV) :
    apiEval fac [("$h", ⟨carrier, heapTy.substTyVars fun _ => .bool, x⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, y⟩)]
      (allocatedT (apiVar "$h") (apiVar "$o")) = some ⟨carrier, .bool, false⟩ := by
  api_eval
  rfl

/-- The model satisfies the heap laws of a program whose fields are all `Box.v` of type `int`. -/
private theorem heapApi {Γ : UnorderedProgram}
    (hn : ∀ n ∈ heapApiNames Γ, n ∈ "Bool.Not" :: apiNames)
    (hf : ∀ r d, (r, d) ∈ programFields Γ → r = ⟨"Box", "v"⟩ ∧ fieldMonoTy Γ d = .int) :
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
    refine ⟨fun _ o ho ha => absurd ha (not_holds_of_fails (allocated_fails hh0 ho)), fun _ => ?_⟩
    obtain ⟨x, rfl⟩ := ofTy hh0
    obtain ⟨y, rfl⟩ := ofTy hh1
    api_eval
    rfl
  onlyModifiesRefl h L hh hL := by
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨l, rfl⟩ := ofTy hL
    api_eval
    exact some_bool (@decide_eq_true _ (Classical.propDecidable _) fun _ _ => rfl)
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
    have hsub' (q : RefV) (hq : (m : LocsV) q = true) : (l : LocsV) q = true :=
      bool_inj ((mem_eval l q ()).symm.trans (hsub ⟨carrier, refTy.substTyVars fun _ => .bool, q⟩
        ⟨carrier, fieldIdTy.substTyVars fun _ => .bool, ()⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        ((mem_eval m q ()).trans (holds_iff.mpr hq))))
    refine (onlyMod_eval x0 x2 l).trans
      (some_bool (@decide_eq_true _ (Classical.propDecidable _) fun q hq => ?_))
    have hm : (m : LocsV) q = false := Bool.eq_false_iff.mpr fun hm => by simp [hsub' q hm] at hq
    exact (h12' q hm).trans (h01' q hq)
  memAt p j o k hp hj ho hk := by
    obtain ⟨yp, rfl⟩ := ofTy hp
    obtain ⟨yj, rfl⟩ := ofTy hj
    obtain ⟨yo, rfl⟩ := ofTy ho
    obtain ⟨yk, rfl⟩ := ofTy hk
    change RefV at yp yo
    have e1 : apiEval fac [("$p", ⟨carrier, refTy.substTyVars fun _ => .bool, yp⟩),
        ("$j", ⟨carrier, _, yj⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, yo⟩), ("$k", ⟨carrier, _, yk⟩)]
        (locsMemT (locsAtT (apiVar "$p") (apiVar "$j")) (apiVar "$o") (apiVar "$k")) =
        some ⟨carrier, .bool, decide (yo = yp)⟩ := by
      api_eval
      rfl
    have e2 : apiEval fac [("$p", ⟨carrier, refTy.substTyVars fun _ => .bool, yp⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, yo⟩)]
        (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")) =
        some ⟨carrier, .bool, @decide (yo = yp) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    have e3 : apiEval fac [("$j", ⟨carrier, _, yj⟩), ("$k", ⟨carrier, _, yk⟩)]
        (.eq Core.coreLoc (apiVar "$k") (apiVar "$j")) =
        some ⟨carrier, .bool, @decide (yk = yj) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    simp only [apiHolds, e1, e2, e3]
    rw [holds, holds, holds]
    simp only [decide_eq_true_eq]
    exact ⟨fun h => ⟨h, Subsingleton.elim (α := Unit) _ _⟩, And.left⟩
  memObject p o k hp ho hk := by
    obtain ⟨yp, rfl⟩ := ofTy hp
    obtain ⟨yo, rfl⟩ := ofTy ho
    obtain ⟨yk, rfl⟩ := ofTy hk
    change RefV at yp yo
    have e1 : apiEval fac [("$p", ⟨carrier, refTy.substTyVars fun _ => .bool, yp⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, yo⟩), ("$k", ⟨carrier, _, yk⟩)]
        (locsMemT (locsObjectT (apiVar "$p")) (apiVar "$o") (apiVar "$k")) =
        some ⟨carrier, .bool, decide (yo = yp)⟩ := by
      api_eval
      rfl
    have e2 : apiEval fac [("$p", ⟨carrier, refTy.substTyVars fun _ => .bool, yp⟩),
        ("$o", ⟨carrier, refTy.substTyVars fun _ => .bool, yo⟩)]
        (.eq Core.coreLoc (apiVar "$o") (apiVar "$p")) =
        some ⟨carrier, .bool, @decide (yo = yp) (Classical.propDecidable _)⟩ := by
      api_eval
      rfl
    simp only [apiHolds, e1, e2]
    rw [holds, holds]
    simp only [decide_eq_true_eq]
  fieldIdsDistinct r d hrd r' d' hrd' hne :=
    absurd ((hf r d hrd).1.trans (hf r' d' hrd').1.symm) hne
  frame r d hrd h0 h1 L o hh0 hh1 hL ho hmod hnot := by
    obtain ⟨rfl, hft⟩ := hf r d hrd
    rw [hft] at hnot ⊢
    obtain ⟨x0, rfl⟩ := ofTy hh0
    obtain ⟨x1, rfl⟩ := ofTy hh1
    obtain ⟨l, rfl⟩ := ofTy hL
    obtain ⟨y, rfl⟩ := ofTy ho
    have hm := @of_decide_eq_true _ (Classical.propDecidable _)
      (bool_inj ((onlyMod_eval x0 x1 l).symm.trans hmod))
    have he : apiEval fac [("$L", ⟨carrier, _, l⟩), ("$o", ⟨carrier, _, y⟩)] (locsMemT (apiVar "$L")
        (apiVar "$o") (fieldIdT .int (fieldConst ⟨"Box", "v"⟩ .int))) =
        some ⟨carrier, .bool, (l : LocsV) y⟩ := by
      api_eval
      rfl
    rw [read_eval x1 y, read_eval x0 y, hm y (bool_inj (he.symm.trans hnot))]
  readWriteSame r d hrd h o w h' hh ho hw hwr := by
    obtain ⟨rfl, hft⟩ := hf r d hrd
    rw [hft] at hw hwr ⊢
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    obtain ⟨z, rfl⟩ := ofTy hw
    cases (write_eval x y z).symm.trans hwr
    exact (read_eval _ y).trans
      (congrArg (fun v => (some ⟨carrier, LSort.int, v⟩ : Option SemValue)) (ite_eq_left rfl))
  writeOnlyModifies r d hrd h o w h' hh ho hw hwr := by
    obtain ⟨rfl, hft⟩ := hf r d hrd
    rw [hft] at hw hwr ⊢
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    obtain ⟨z, rfl⟩ := ofTy hw
    change RefV at y
    cases (write_eval x y z).symm.trans hwr
    api_eval
    refine some_bool (@decide_eq_true _ (Classical.propDecidable _) fun p hp => ?_)
    have hp' : decide (p = y) = false := hp
    exact ite_eq_right (fun h => by simp [h] at hp')
  writeKeepsAllocated r d hrd h o w h' p hh ho hw hp hwr := by
    obtain ⟨rfl, hft⟩ := hf r d hrd
    rw [hft] at hw hwr
    obtain ⟨x, rfl⟩ := ofTy hh
    obtain ⟨y, rfl⟩ := ofTy ho
    obtain ⟨z, rfl⟩ := ofTy hw
    obtain ⟨q, rfl⟩ := ofTy hp
    cases (write_eval x y z).symm.trans hwr
    exact (allocated_eval _ q).trans (allocated_eval x q).symm

/-! ## The programs -/

/-- A body of one block, `b0`, running `cmds` and returning. -/
private def oneBlock (cmds : List IRCmd) : Body :=
  { cfg := { entry := "b0", blocks := [("b0", { cmds, transfer := .finish .empty })] },
    handlers := [] }

/-- The body of `main`: it declares `x : int := 0` and calls `g`. -/
private def mainBody : Body :=
  oneBlock [.cmd (.init ⟨"x", ()⟩ (.forAll [] .int) (.det (.intConst Core.coreLoc 0)) .empty),
    .call [] "g" [] .empty]

/-- A program without composites: `g` returns at once, and `main` declares an `int` local and
calls `g`. -/
private def noComposites : UnorderedProgram :=
  { composites := [],
    procedures := [
      { name := "g", inputs := [], outputs := [], throws := none, body := some (oneBlock []) },
      { name := "main", inputs := [], outputs := [], throws := none, body := some mainBody }] }

/-- `noComposites` with the composite `Box`, whose one field `v` has type `int`. -/
private def withBox : UnorderedProgram :=
  { noComposites with
    composites :=
      [{ name := "Box", extending := [], fields := [{ name := "v", ty := .forAll [] .int }] }] }

/-- The frame of a run of `main`. -/
private def mainFrame : Frame := ⟨mainBody, none, [], [], []⟩

/-- The heap the runs start from: every field of every reference holds 0. -/
private def heap₀ : SemValue := ⟨carrier, .tcons "Heap" [], fun (_ : Option Int) => (0 : Int)⟩

/-- The initial environment: only `$entryHeap` is bound, to `heap₀`, and the factory is the
model's. -/
private noncomputable def env₀ : Imperative.Env Core.Expression :=
  ⟨fun x => if x = entryHeapVar then some heap₀ else none, fac⟩

/-- The initial-environment well-formedness `CortexInitEnvWF` holds for `main` in a program
whose composites, fields and API names the model covers, and whose globals and parameters are
not named `$entryHeap`. -/
private theorem initEnvWF_of {Γ : UnorderedProgram} (params : Core.Logic.InitEnvWFParams)
    (hr : ∀ n ∈ refTagNames Γ, n ∈ "Bool.Not" :: apiNames)
    (hc : ∀ c ∈ Γ.composites, c.name = "Box")
    (hh : ∀ n ∈ heapApiNames Γ, n ∈ "Bool.Not" :: apiNames)
    (hf : ∀ r d, (r, d) ∈ programFields Γ → r = ⟨"Box", "v"⟩ ∧ fieldMonoTy Γ d = .int)
    (hp : ∀ p ∈ Γ.procedures, ∀ b, p.body = some b →
      (p.inputs.map Prod.fst).Nodup ∧ (p.outputs.map Prod.fst).Nodup ∧ b.checkHandlers Γ = .ok ())
    (hfree : ∀ xt, (xt ∈ Γ.globals ∨ ∃ p ∈ Γ.procedures, xt ∈ p.inputs ++ p.outputs) →
      xt.1 ≠ entryHeapVar) :
    CortexInitEnvWF Γ params mainFrame env₀ where
  toWellFormedSemanticEval := Core.coreEvaluator_WellFormedSemanticEval fac
    (get_funcs funcs_nodup (g := (boolNotFunc (T := Core.CoreLParams)).func) (by simp [funcs]))
  storeWellDefined x v h := by
    simp only [env₀] at h
    split at h
    · cases h
      rfl
    · cases h
  refTag := refTag hr hc
  heapApi := heapApi hh hf
  procsWF := hp
  entryHandlers := rfl
  entryReadsDefined x hx := by
    simp [mainFrame, mainBody, oneBlock, Body.used, IRCmd.exprs, IRCmd.updated,
      HasFvars.getFvars, LExpr.LExpr.getVars] at hx
  globalsTyped xt hx v h := by simp [env₀, hfree xt (.inl hx)] at h
  paramsTyped p hp _ xt hx v h := by simp [env₀, hfree xt (.inr ⟨p, hp, hx⟩)] at h
  entryHeap := ⟨heap₀, by simp [env₀], ⟨rfl, rfl⟩,
    fun _ ho ha => absurd ha (not_holds_of_fails (allocated_fails ⟨rfl, rfl⟩ ho))⟩
  reservedFresh n hn h := by
    simp [env₀, hn] at h


/-- The procedures of both programs have no parameters and no handlers. -/
private theorem procsWF {Γ : UnorderedProgram} (hΓ : Γ.procedures = noComposites.procedures) :
    ∀ p ∈ Γ.procedures, ∀ b, p.body = some b →
      (p.inputs.map Prod.fst).Nodup ∧ (p.outputs.map Prod.fst).Nodup ∧
        b.checkHandlers Γ = .ok () := by
  intro p hp b hb
  simp only [hΓ, noComposites, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> cases hb <;> exact ⟨.nil, .nil, rfl⟩

/-- `CortexInitEnvWF` holds for `main` of the program without composites. -/
theorem initEnvWF_noComposites (params : Core.Logic.InitEnvWFParams) :
    ∃ ρ, CortexInitEnvWF noComposites params mainFrame ρ :=
  ⟨env₀, initEnvWF_of params (by decide) nofun (by decide) (by simp [programFields, noComposites])
    (procsWF rfl) (by simp [noComposites])⟩

/-- `CortexInitEnvWF` holds for `main` of the program with the composite `Box`. -/
theorem initEnvWF_box (params : Core.Logic.InitEnvWFParams) :
    ∃ ρ, CortexInitEnvWF withBox params mainFrame ρ :=
  ⟨env₀, initEnvWF_of params (by decide) (by decide) (by decide)
    (by simp [programFields, withBox, fieldMonoTy, eraseMono, eraseRefs, eraseRefsList,
      constrainedValueTy, constrainedBase, isRefName, UnorderedProgram.findComposite?,
      noComposites]; rfl) (procsWF rfl) (by simp [withBox, noComposites])⟩

/-- The program without composites is in the domain of `Ordering.order`. -/
theorem noComposites_order : ∃ q, Ordering.order noComposites = .ok q := ⟨_, rfl⟩

/-! ## No vacuous premise

The initial-environment well-formedness `CortexInitEnvWF` is satisfiable on programs without
composites, so a trace-inclusion theorem about a pass whose input has none says something
about its traces. -/

/-- Some program without composites has an initial environment that satisfies the Cortex
initial-environment well-formedness `CortexInitEnvWF`. -/
theorem initEnvWF_without_composites_satisfiable (params : Core.Logic.InitEnvWFParams) :
    ¬ ∀ (Γ : UnorderedProgram) fr ρ, Γ.composites = [] → ¬ CortexInitEnvWF Γ params fr ρ :=
  fun h =>
    have ⟨ρ, hρ⟩ := initEnvWF_noComposites params
    h _ _ ρ rfl hρ

/-- Some program that `Ordering.order` accepts has an initial environment that satisfies the
Cortex initial-environment well-formedness `CortexInitEnvWF`. -/
theorem initEnvWF_ordered_satisfiable (params : Core.Logic.InitEnvWFParams) :
    ¬ ∀ (p : UnorderedProgram) q fr ρ, Ordering.order p = .ok q →
      ¬ CortexInitEnvWF p params fr ρ :=
  fun h =>
    have ⟨ρ, hρ⟩ := initEnvWF_noComposites params
    have ⟨_, hq⟩ := noComposites_order
    h _ _ _ ρ hq hρ

end Cortex.Sem.InitEnvWFExamples
