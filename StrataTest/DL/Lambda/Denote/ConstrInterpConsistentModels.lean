/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteConstrs
import all Strata.DL.Lambda.FactoryProps

/-!
## Test: models of the datatype properties

Datatypes interpreted by Lean types satisfy `ConstrInterpConsistent`. This
shows that its properties are jointly satisfiable by nonempty datatypes:
- `Nat := zero | succ Nat`, interpreted by Lean's `Nat`.
- `IntList := nil | cons (hd : int) (tl : IntList)`, interpreted by Lean's
  `List Int`. It has an argument of a non-datatype sort next to a recursive one.
- `Option a := none | some (x : a)`, a polymorphic datatype, interpreted by
  Lean's `Option`, for every sort `a`.
- `Even := zero | succE (o : Odd)` and `Odd := succO (e : Even)`, a mutually
  recursive pair, interpreted by a mutual inductive type.

The theorem for `Nat` uses `constr_induction_on`. A type constructor
interpretation cannot refer to `SortDenote` of the interpretation being
defined. So the `Option` model defines the carrier of each sort by recursion on
the sort and proves it equals `SortDenote`.
-/

namespace Lambda

/-- Parameters with unit metadata. -/
private abbrev TP : LExprParams := ⟨Unit, Unit⟩

/-- A factory built from a list of functions with distinct names has exactly
those functions as members. -/
private theorem mem_ofArray {T} (l : List (LFunc T))
    (hnodup : List.Nodup (l.map (·.name.name))) (f : LFunc T) :
    f ∈ (Factory.ofArray l.toArray).toArray ↔ f ∈ l := by
  constructor
  · intro hf
    exact List.mem_toArray.mp (Factory.ofArray_mem hf)
  · intro hmem
    have hmem' : f ∈ l.toArray := List.mem_toArray.mpr hmem
    have hnodup' : List.Nodup (l.toArray.toList.map (·.name.name)) := by
      rw [List.toList_toArray]
      exact hnodup
    have hget := Factory.get?_ofArray_of_mem hmem' hnodup'
    exact (Factory.getElem?_eq_some_iff'.mp hget).1

/-! ### Natural numbers -/

/-- The constructor `zero`. -/
private def zeroC : LConstr Unit := ⟨⟨"zero", ()⟩, [], "isZero"⟩

/-- The constructor `succ`. -/
private def succC : LConstr Unit :=
  ⟨⟨"succ", ()⟩, [(⟨"pred", ()⟩, .tcons "Nat" [])], "isSucc"⟩

/-- The datatype `Nat := zero | succ Nat`. -/
private def natD : LDatatype Unit :=
  { name := "Nat", typeArgs := [], constrs := [zeroC, succC], constrs_ne := rfl }

/-- The constructor function `zero`. -/
private def zeroF : LFunc TP := constrFunc zeroC natD

/-- The constructor function `succ`. -/
private def succF : LFunc TP := constrFunc succC natD

/-- The factory of the constructors of `Nat`. -/
private def natF : @Factory TP := Factory.ofArray #[zeroF, succF]

/-- The factory contains exactly the two constructors. -/
private theorem mem_natF (f : LFunc TP) :
    f ∈ natF.toArray ↔ f = zeroF ∨ f = succF := by
  have hnodup : List.Nodup ([zeroF, succF].map (·.name.name)) := by
    simp [zeroF, succF, zeroC, succC, constrFunc]
  have hmem := mem_ofArray [zeroF, succF] hnodup f
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hmem

/-- Interprets the type constructor `Nat` as Lean's `Nat`. -/
private def natTc : TyConstrInterp := fun name _ => if name = "Nat" then Nat else PUnit

/-- Every sort of `natTc` has an element. -/
private instance natTc_allInhabited : TyConstrInterp.AllInhabited natTc where
  inhabited name _ := by
    unfold natTc
    split <;> exact ⟨default⟩

/-- Interprets `zero` as `0` and `succ` as the successor function. -/
private noncomputable def natOp : OpInterp natTc := fun name s =>
  match name, s with
  | "zero", .tcons "Nat" [] => (0 : Nat)
  | "succ", .tcons "arrow" [.tcons "Nat" [], .tcons "Nat" []] => Nat.succ
  | _, _ => default

example : constrApp natTc natOp zeroF (fun _ => .bool) .nil = (0 : Nat) := rfl
example (n : Nat) :
    constrApp natTc natOp succF (fun _ => .bool) (.cons n .nil) = n.succ := rfl

/-- Every function of the factory is `zero` or `succ`. -/
private theorem natF_cases (f : LFunc TP) (hf : f ∈ natF.toArray) :
    f = zeroF ∨ f = succF := (mem_natF f).mp hf

/-- Both constructors return the sort `Nat`. -/
private theorem natF_output (f : LFunc TP) (hf : f ∈ natF.toArray) (vt : TyVarVal) :
    LMonoTy.substTyVars vt f.output = .tcons "Nat" [] := by
  rcases natF_cases f hf with rfl | rfl <;> rfl

/-- `Nat` is a datatype sort of the factory. -/
private theorem natF_isDatatypeSort : natF.IsDatatypeSort (.tcons "Nat" []) :=
  ⟨zeroF, (mem_natF zeroF).mpr (Or.inl rfl), rfl, fun _ => .bool, rfl⟩

/-- `Nat` is the only datatype sort of the factory. -/
private theorem natF_isDatatypeSort_eq (s : LSort) :
    natF.IsDatatypeSort s → s = .tcons "Nat" [] := by
  intro h
  obtain ⟨f, hf, _, vt, hs⟩ := h
  rw [← hs]
  exact natF_output f hf vt

/-- The model satisfies disjointness, injectivity and induction. -/
private theorem natConsistent : ConstrInterpConsistent natTc natOp natF := by
  constructor
  · intro f1 f2 h1 h2 _ _ hne vt
    dsimp only
    intro heq args1 args2
    rcases natF_cases f1 h1 with rfl | rfl <;> rcases natF_cases f2 h2 with rfl | rfl
    · exact absurd rfl hne
    · change HList (SortDenote natTc) [] at args1
      change HList (SortDenote natTc) [.tcons "Nat" []] at args2
      cases args1
      rcases args2 with _ | ⟨n, args2⟩
      cases args2
      intro h
      change (0 : Nat) = Nat.succ n at h
      exact Nat.noConfusion h
    · change HList (SortDenote natTc) [] at args2
      change HList (SortDenote natTc) [.tcons "Nat" []] at args1
      cases args2
      rcases args1 with _ | ⟨n, args1⟩
      cases args1
      intro h
      change Nat.succ n = (0 : Nat) at h
      exact Nat.noConfusion h
    · exact absurd rfl hne
  · intro f hf _ vt
    dsimp only
    intro args1 args2 h
    rcases natF_cases f hf with rfl | rfl
    · change HList (SortDenote natTc) [] at args1 args2
      cases args1
      cases args2
      rfl
    · change HList (SortDenote natTc) [.tcons "Nat" []] at args1 args2
      rcases args1 with _ | ⟨n, args1⟩
      rcases args2 with _ | ⟨m, args2⟩
      cases args1
      cases args2
      change Nat.succ n = Nat.succ m at h
      have hnm : n = m := Nat.succ.inj h
      subst hnm
      rfl
  · intro P hstep s v hs
    have hsn := natF_isDatatypeSort_eq s hs
    subst hsn
    change Nat at v
    induction v with
    | zero =>
      exact hstep zeroF ((mem_natF zeroF).mpr (Or.inl rfl)) rfl (fun _ => .bool) .nil trivial
    | succ n ih =>
      exact hstep succF ((mem_natF succF).mpr (Or.inr rfl)) rfl (fun _ => .bool)
        (.cons n .nil) ⟨fun _ => ih, trivial⟩

/-- A value of a sort equal to `Nat` read as a Lean `Nat`. -/
private def natVal {s : LSort} (h : s = .tcons "Nat" []) (x : SortDenote natTc s) : Nat :=
  cast (congrArg (SortDenote natTc) h) x

/-- Induction over the single datatype sort `Nat` through `constr_induction_on`:
adding zero on the left is the identity. The successor case uses the induction
hypothesis. -/
private theorem nat_sort_induction (v : SortDenote natTc (.tcons "Nat" [])) :
    0 + natVal rfl v = natVal rfl v := by
  have hS : ∀ s : LSort, s = .tcons "Nat" [] → natF.IsDatatypeSort s := by
    intro s hs
    subst hs
    exact natF_isDatatypeSort
  have hstep : ∀ f ∈ natF.toArray, f.isConstr = true → ∀ (vt : TyVarVal)
      (args : HList (SortDenote natTc) (f.inputs.values.map (LMonoTy.substTyVars vt))),
        LMonoTy.substTyVars vt f.output = .tcons "Nat" [] →
        HList.All (fun s x => s = .tcons "Nat" [] →
          ∀ h : s = .tcons "Nat" [], 0 + natVal h x = natVal h x) args →
        ∀ h : LMonoTy.substTyVars vt f.output = .tcons "Nat" [],
          0 + natVal h (constrApp natTc natOp f vt args) =
            natVal h (constrApp natTc natOp f vt args) := by
    intro f hf _ vt args _ hall h
    rcases natF_cases f hf with rfl | rfl
    · change HList (SortDenote natTc) [] at args
      cases args
      rfl
    · change HList (SortDenote natTc) [.tcons "Nat" []] at args
      rcases args with _ | ⟨n, args⟩
      cases args
      obtain ⟨hn, -⟩ := hall
      have hih : 0 + natVal rfl n = natVal rfl n := hn rfl rfl
      change 0 + Nat.succ (natVal rfl n) = Nat.succ (natVal rfl n)
      rw [Nat.add_succ, hih]
  have hind := constr_induction_on natConsistent (· = .tcons "Nat" []) hS
    (fun s x => ∀ h : s = .tcons "Nat" [], 0 + natVal h x = natVal h x) hstep
  exact hind _ v rfl rfl

/-! ### Lists of integers -/

/-- The constructor `nil`. -/
private def nilC : LConstr Unit := ⟨⟨"nil", ()⟩, [], "isNil"⟩

/-- The constructor `cons`. -/
private def consC : LConstr Unit :=
  ⟨⟨"cons", ()⟩, [(⟨"hd", ()⟩, .int), (⟨"tl", ()⟩, .tcons "IntList" [])], "isCons"⟩

/-- The datatype `IntList := nil | cons (hd : int) (tl : IntList)`. -/
private def listD : LDatatype Unit :=
  { name := "IntList", typeArgs := [], constrs := [nilC, consC], constrs_ne := rfl }

/-- The constructor function `nil`. -/
private def nilF : LFunc TP := constrFunc nilC listD

/-- The constructor function `cons`. -/
private def consF : LFunc TP := constrFunc consC listD

/-- The factory of the constructors of `IntList`. -/
private def listF : @Factory TP := Factory.ofArray #[nilF, consF]

/-- The factory contains exactly the two constructors. -/
private theorem mem_listF (f : LFunc TP) :
    f ∈ listF.toArray ↔ f = nilF ∨ f = consF := by
  have hnodup : List.Nodup ([nilF, consF].map (·.name.name)) := by
    simp [nilF, consF, nilC, consC, constrFunc]
  have hmem := mem_ofArray [nilF, consF] hnodup f
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hmem

/-- Interprets the type constructor `IntList` as Lean's `List Int`. -/
private def listTc : TyConstrInterp := fun name _ => if name = "IntList" then List Int else PUnit

/-- Every sort of `listTc` has an element. -/
private instance listTc_allInhabited : TyConstrInterp.AllInhabited listTc where
  inhabited name _ := by
    unfold listTc
    split <;> exact ⟨default⟩

/-- Interprets `nil` as the empty list and `cons` as list construction. -/
private noncomputable def listOp : OpInterp listTc := fun name s =>
  match name, s with
  | "nil", .tcons "IntList" [] => ([] : List Int)
  | "cons", .tcons "arrow" [.tcons "int" [],
      .tcons "arrow" [.tcons "IntList" [], .tcons "IntList" []]] =>
    fun (hd : Int) (tl : List Int) => hd :: tl
  | _, _ => default

example : constrApp listTc listOp nilF (fun _ => .bool) .nil = ([] : List Int) := rfl
example :
    constrApp listTc listOp consF (fun _ => .bool) (.cons (1 : Int) (.cons ([] : List Int) .nil))
      = [(1 : Int)] := rfl

/-- Every function of the factory is `nil` or `cons`. -/
private theorem listF_cases (f : LFunc TP) (hf : f ∈ listF.toArray) :
    f = nilF ∨ f = consF := (mem_listF f).mp hf

/-- Both constructors return the sort `IntList`. -/
private theorem listF_output (f : LFunc TP) (hf : f ∈ listF.toArray) (vt : TyVarVal) :
    LMonoTy.substTyVars vt f.output = .tcons "IntList" [] := by
  rcases listF_cases f hf with rfl | rfl <;> rfl

/-- `IntList` is the only datatype sort of the factory. -/
private theorem listF_isDatatypeSort_eq (s : LSort) :
    listF.IsDatatypeSort s → s = .tcons "IntList" [] := by
  intro h
  obtain ⟨f, hf, _, vt, hs⟩ := h
  rw [← hs]
  exact listF_output f hf vt

/-- The integer sort is not a datatype sort of the factory. -/
private theorem listF_int_not_datatypeSort : ¬ listF.IsDatatypeSort (.tcons "int" []) := by
  intro h
  have heq := listF_isDatatypeSort_eq _ h
  simp only [LSort.tcons.injEq] at heq
  exact absurd heq.1 (by decide)

/-- The model satisfies disjointness, injectivity and induction. -/
private theorem listConsistent : ConstrInterpConsistent listTc listOp listF := by
  constructor
  · intro f1 f2 h1 h2 _ _ hne vt
    dsimp only
    intro heq args1 args2
    rcases listF_cases f1 h1 with rfl | rfl <;> rcases listF_cases f2 h2 with rfl | rfl
    · exact absurd rfl hne
    · change HList (SortDenote listTc) [] at args1
      change HList (SortDenote listTc) [.tcons "int" [], .tcons "IntList" []] at args2
      cases args1
      rcases args2 with _ | ⟨x, args2⟩
      rcases args2 with _ | ⟨l, args2⟩
      cases args2
      intro h
      change ([] : List Int) = x :: l at h
      cases h
    · change HList (SortDenote listTc) [] at args2
      change HList (SortDenote listTc) [.tcons "int" [], .tcons "IntList" []] at args1
      cases args2
      rcases args1 with _ | ⟨x, args1⟩
      rcases args1 with _ | ⟨l, args1⟩
      cases args1
      intro h
      change x :: l = ([] : List Int) at h
      cases h
    · exact absurd rfl hne
  · intro f hf _ vt
    dsimp only
    intro args1 args2 h
    rcases listF_cases f hf with rfl | rfl
    · change HList (SortDenote listTc) [] at args1 args2
      cases args1
      cases args2
      rfl
    · change HList (SortDenote listTc) [.tcons "int" [], .tcons "IntList" []] at args1 args2
      rcases args1 with _ | ⟨x, args1⟩
      rcases args1 with _ | ⟨l, args1⟩
      rcases args2 with _ | ⟨y, args2⟩
      rcases args2 with _ | ⟨m, args2⟩
      cases args1
      cases args2
      change x :: l = y :: m at h
      obtain ⟨hxy, hlm⟩ := List.cons.inj h
      subst hxy
      subst hlm
      rfl
  · intro P hstep s v hs
    have hsl := listF_isDatatypeSort_eq s hs
    subst hsl
    change List Int at v
    induction v with
    | nil =>
      exact hstep nilF ((mem_listF nilF).mpr (Or.inl rfl)) rfl (fun _ => .bool) .nil trivial
    | cons x l ih =>
      exact hstep consF ((mem_listF consF).mpr (Or.inr rfl)) rfl (fun _ => .bool)
        (.cons x (.cons l .nil))
        ⟨fun hint => absurd hint listF_int_not_datatypeSort, fun _ => ih, trivial⟩

/-! ### Optional values

`Option a := none | some (x : a)` has a type parameter. One interpretation
satisfies the properties for every sort `a`. -/

/-- The constructor `none`. -/
private def noneC : LConstr Unit := ⟨⟨"none", ()⟩, [], "isNone"⟩

/-- The constructor `some`. -/
private def someC : LConstr Unit :=
  ⟨⟨"some", ()⟩, [(⟨"x", ()⟩, .ftvar "a")], "isSome"⟩

/-- The datatype `Option a := none | some (x : a)`. -/
private def optD : LDatatype Unit :=
  { name := "Option", typeArgs := ["a"], constrs := [noneC, someC],
    constrs_ne := rfl }

/-- The constructor function `none`. -/
private def noneF : LFunc TP := constrFunc noneC optD

/-- The constructor function `some`. -/
private def someF : LFunc TP := constrFunc someC optD

/-- The factory of the constructors of `Option`. -/
private def optF : @Factory TP := Factory.ofArray #[noneF, someF]

/-- The factory contains exactly the two constructors. -/
private theorem mem_optF (f : LFunc TP) :
    f ∈ optF.toArray ↔ f = noneF ∨ f = someF := by
  have hnodup : List.Nodup ([noneF, someF].map (·.name.name)) := by
    simp [noneF, someF, noneC, someC, constrFunc]
  have hmem := mem_ofArray [noneF, someF] hnodup f
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hmem

/-- The carrier of a sort: as `SortDenote`, except that `Option s` is Lean's
`Option` of the carrier of `s`. -/
private def optCarrier : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Strata.Util.Real
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => optCarrier a → optCarrier b
  | .tcons "Map" [k, v]   => optCarrier k → optCarrier v
  | .tcons "Sequence" [a] => List (optCarrier a)
  | .tcons "Option" [a]   => Option (optCarrier a)
  | .tcons _ _            => PUnit

/-- Interprets the type constructor `Option` at every argument sort as Lean's
`Option` of the carrier of the argument. -/
private def optTc : TyConstrInterp := fun name args =>
  match name, args with
  | "Option", [a] => Option (optCarrier a)
  | _, _ => PUnit

/-- Every sort of `optTc` has an element. -/
private instance optTc_allInhabited : TyConstrInterp.AllInhabited optTc where
  inhabited name args := by
    unfold optTc
    split <;> exact ⟨default⟩

/-- Under `optTc`, every sort denotes its carrier. -/
private theorem sortDenote_optTc (s : LSort) :
    SortDenote optTc s = optCarrier s := by
  induction s using LSort.rec' with
  | htcons name args ih =>
    unfold SortDenote
    split
    all_goals try
      (rename_i heq
       simp only [LSort.tcons.injEq] at heq
       obtain ⟨rfl, rfl⟩ := heq
       rfl)
    · rename_i heq
      cases heq
    · rename_i a b heq
      simp only [LSort.tcons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have ha : SortDenote optTc a = optCarrier a := ih a (by simp)
      have hb : SortDenote optTc b = optCarrier b := ih b (by simp)
      rw [ha, hb]
      rfl
    · rename_i k v heq
      simp only [LSort.tcons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hk : SortDenote optTc k = optCarrier k := ih k (by simp)
      have hv : SortDenote optTc v = optCarrier v := ih v (by simp)
      rw [hk, hv]
      rfl
    · rename_i a heq
      simp only [LSort.tcons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have ha : SortDenote optTc a = optCarrier a := ih a (by simp)
      rw [ha]
      rfl
    · rename_i hbool hint hreal hstring harrow hmap hseq
      simp only [LSort.tcons.injEq] at hseq
      obtain ⟨rfl, rfl⟩ := hseq
      unfold optCarrier optTc
      split <;> split <;>
        first
        | rfl
        | (exfalso; simp_all; done)
        | (rename_i heq
           simp only [LSort.tcons.injEq, List.cons.injEq, and_true,
             true_and] at heq
           subst heq
           rfl)
        | (exfalso
           rename_i hneg heq
           simp only [LSort.tcons.injEq] at heq
           obtain ⟨rfl, rfl⟩ := heq
           exact hneg _ rfl rfl)
  | hbitvec n => rfl

/-- Reads a value of sort `s` as an element of its carrier. -/
private def toCarrier {s : LSort} (x : SortDenote optTc s) : optCarrier s :=
  cast (sortDenote_optTc s) x

/-- Reads an element of the carrier of `s` as a value of sort `s`. -/
private def ofCarrier {s : LSort} (x : optCarrier s) : SortDenote optTc s :=
  cast (sortDenote_optTc s).symm x

/-- The function `some` at argument sort `a` and result sort `Option b`. It is
`none` unless `a = b`; the properties never reach the case `a ≠ b`. -/
private def optSome (a b : LSort) :
    SortDenote optTc (.tcons "arrow" [a, .tcons "Option" [b]]) :=
  fun x =>
    (if h : a = b then
        some (toCarrier (cast (congrArg (SortDenote optTc) h) x))
      else none : Option (optCarrier b))

/-- Interprets `none` as `Option.none` and `some` as `Option.some`, at every
instance of `Option`. -/
private noncomputable def optOp : OpInterp optTc := fun name s =>
  match name, s with
  | "none", .tcons "Option" [a] => (none : Option (optCarrier a))
  | "some", .tcons "arrow" [a, .tcons "Option" [b]] => optSome a b
  | _, _ => default

example (a : LSort) :
    constrApp optTc optOp noneF (fun _ => a) .nil =
      (none : Option (optCarrier a)) := rfl

/-- Applying `some` gives `Option.some` of the argument. -/
private theorem optOp_some (a : LSort) (x : SortDenote optTc a) :
    SortDenote.applyArgs optTc
      (optOp "some" (LSort.mkArrow (.tcons "Option" [a]) [a]))
      (.cons x .nil) = (some (toCarrier x) : Option (optCarrier a)) := by
  change optSome a a x = _
  unfold optSome
  simp only [↓reduceDIte]
  rfl

/-- Reading a value as a carrier element is injective. -/
private theorem toCarrier_injective {s : LSort} {x y : SortDenote optTc s}
    (h : toCarrier x = toCarrier y) : x = y := by
  have hinj : cast (sortDenote_optTc s).symm (cast (sortDenote_optTc s) x) =
      cast (sortDenote_optTc s).symm (cast (sortDenote_optTc s) y) :=
    congrArg (cast (sortDenote_optTc s).symm) h
  simpa only [cast_cast, cast_eq] using hinj

/-- Reading a value as a carrier element and back is the identity. -/
private theorem toCarrier_ofCarrier {s : LSort} (x : optCarrier s) :
    toCarrier (ofCarrier x : SortDenote optTc s) = x := by
  simp only [toCarrier, ofCarrier, cast_cast, cast_eq]

/-- Every function of the factory is `none` or `some`. -/
private theorem optF_cases (f : LFunc TP) (hf : f ∈ optF.toArray) :
    f = noneF ∨ f = someF := (mem_optF f).mp hf

/-- Both constructors return the sort `Option a` for the sort `a` that the
valuation gives the type variable. -/
private theorem optF_output (f : LFunc TP) (hf : f ∈ optF.toArray)
    (vt : TyVarVal) :
    LMonoTy.substTyVars vt f.output = .tcons "Option" [vt "a"] := by
  rcases optF_cases f hf with rfl | rfl <;> rfl

/-- Every datatype sort of the factory is `Option a` for some sort `a`. -/
private theorem optF_isDatatypeSort_eq (s : LSort)
    (hs : optF.IsDatatypeSort s) :
    ∃ a, s = .tcons "Option" [a] := by
  obtain ⟨f, hf, _, vt, hout⟩ := hs
  exact ⟨vt "a", by rw [← hout]; exact optF_output f hf vt⟩

/-- The model satisfies disjointness, injectivity and induction, for every
instance of `Option`. -/
private theorem optConsistent : ConstrInterpConsistent optTc optOp optF := by
  constructor
  · intro f1 f2 h1 h2 _ _ hne vt
    dsimp only
    intro heq args1 args2
    rcases optF_cases f1 h1 with rfl | rfl <;>
      rcases optF_cases f2 h2 with rfl | rfl
    · exact absurd rfl hne
    · change HList (SortDenote optTc) [] at args1
      change HList (SortDenote optTc) [vt "a"] at args2
      cases args1
      rcases args2 with _ | ⟨x, args2⟩
      cases args2
      intro h
      change (none : Option (optCarrier (vt "a"))) =
        SortDenote.applyArgs optTc
          (optOp "some" (LSort.mkArrow (.tcons "Option" [vt "a"]) [vt "a"]))
          (.cons x .nil) at h
      rw [optOp_some] at h
      cases h
    · change HList (SortDenote optTc) [] at args2
      change HList (SortDenote optTc) [vt "a"] at args1
      cases args2
      rcases args1 with _ | ⟨x, args1⟩
      cases args1
      intro h
      change SortDenote.applyArgs optTc
          (optOp "some" (LSort.mkArrow (.tcons "Option" [vt "a"]) [vt "a"]))
          (.cons x .nil) = (none : Option (optCarrier (vt "a"))) at h
      rw [optOp_some] at h
      cases h
    · exact absurd rfl hne
  · intro f hf _ vt
    dsimp only
    intro args1 args2 h
    rcases optF_cases f hf with rfl | rfl
    · change HList (SortDenote optTc) [] at args1 args2
      cases args1
      cases args2
      rfl
    · change HList (SortDenote optTc) [vt "a"] at args1 args2
      rcases args1 with _ | ⟨x, args1⟩
      rcases args2 with _ | ⟨y, args2⟩
      cases args1
      cases args2
      change SortDenote.applyArgs optTc
          (optOp "some" (LSort.mkArrow (.tcons "Option" [vt "a"]) [vt "a"]))
          (.cons x .nil) =
        SortDenote.applyArgs optTc
          (optOp "some" (LSort.mkArrow (.tcons "Option" [vt "a"]) [vt "a"]))
          (.cons y .nil) at h
      rw [optOp_some, optOp_some] at h
      have hxy : toCarrier x = toCarrier y := Option.some.inj h
      have hxy' : x = y := toCarrier_injective hxy
      subst hxy'
      rfl
  · intro P hstep s
    induction s using LSort.rec' with
    | htcons name args ih =>
      intro v hs
      obtain ⟨a, ha⟩ := optF_isDatatypeSort_eq _ hs
      simp only [LSort.tcons.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      change Option (optCarrier a) at v
      cases v with
      | none =>
        exact hstep noneF ((mem_optF noneF).mpr (Or.inl rfl)) rfl (fun _ => a)
          .nil trivial
      | some x =>
        have hall : HList.All (fun s x => optF.IsDatatypeSort s → P s x)
            (HList.cons (ofCarrier x : SortDenote optTc a) HList.nil) :=
          ⟨fun hds => ih a (by simp) _ hds, trivial⟩
        have hres := hstep someF ((mem_optF someF).mpr (Or.inr rfl)) rfl
          (fun _ => a) (.cons (ofCarrier x) .nil) hall
        have hval : constrApp optTc optOp someF (fun _ => a)
            (.cons (ofCarrier x) .nil) = (some x : Option (optCarrier a)) := by
          have happ := optOp_some a (ofCarrier x)
          rw [toCarrier_ofCarrier] at happ
          exact happ
        rw [hval] at hres
        exact hres
    | hbitvec n =>
      intro v hs
      obtain ⟨a, ha⟩ := optF_isDatatypeSort_eq _ hs
      cases ha

/-! ### Mutually recursive datatypes

`Even := zero | succE (o : Odd)` and `Odd := succO (e : Even)` form one block.
`succE` and `succO` each take an argument of the other datatype's sort. -/

mutual
/-- The carrier of `Even`. -/
private inductive EvenN : Type
  | zero : EvenN
  | succE : OddN → EvenN

/-- The carrier of `Odd`. -/
private inductive OddN : Type
  | succO : EvenN → OddN
end

/-- The constructor `zero` of `Even`. -/
private def zeroEC : LConstr Unit := ⟨⟨"zero", ()⟩, [], "isZero"⟩

/-- The constructor `succE` of `Even`. -/
private def succEC : LConstr Unit :=
  ⟨⟨"succE", ()⟩, [(⟨"o", ()⟩, .tcons "Odd" [])], "isSuccE"⟩

/-- The constructor `succO` of `Odd`. -/
private def succOC : LConstr Unit :=
  ⟨⟨"succO", ()⟩, [(⟨"e", ()⟩, .tcons "Even" [])], "isSuccO"⟩

/-- The datatype `Even := zero | succE (o : Odd)`. -/
private def evenD : LDatatype Unit :=
  { name := "Even", typeArgs := [], constrs := [zeroEC, succEC],
    constrs_ne := rfl }

/-- The datatype `Odd := succO (e : Even)`. -/
private def oddD : LDatatype Unit :=
  { name := "Odd", typeArgs := [], constrs := [succOC], constrs_ne := rfl }

/-- The constructor function `zero`. -/
private def zeroEF : LFunc TP := constrFunc zeroEC evenD

/-- The constructor function `succE`. -/
private def succEF : LFunc TP := constrFunc succEC evenD

/-- The constructor function `succO`. -/
private def succOF : LFunc TP := constrFunc succOC oddD

/-- The factory of the constructors of the block `Even`, `Odd`. -/
private def evenF : @Factory TP := Factory.ofArray #[zeroEF, succEF, succOF]

/-- The factory contains exactly the three constructors. -/
private theorem mem_evenF (f : LFunc TP) :
    f ∈ evenF.toArray ↔ f = zeroEF ∨ f = succEF ∨ f = succOF := by
  have hnodup : List.Nodup ([zeroEF, succEF, succOF].map (·.name.name)) := by
    simp [zeroEF, succEF, succOF, zeroEC, succEC, succOC, constrFunc]
  have hmem := mem_ofArray [zeroEF, succEF, succOF] hnodup f
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hmem

/-- Interprets `Even` and `Odd` as the two types of the mutual block. -/
private def evenTc : TyConstrInterp := fun name args =>
  match name, args with
  | "Even", [] => EvenN
  | "Odd", [] => OddN
  | _, _ => PUnit

/-- Every sort of `evenTc` has an element. -/
private instance evenTc_allInhabited : TyConstrInterp.AllInhabited evenTc where
  inhabited name args := by
    unfold evenTc
    split
    · exact ⟨EvenN.zero⟩
    · exact ⟨OddN.succO EvenN.zero⟩
    · exact ⟨default⟩

/-- Interprets the three constructors as those of the mutual block. -/
private noncomputable def evenOp : OpInterp evenTc := fun name s =>
  match name, s with
  | "zero", .tcons "Even" [] => EvenN.zero
  | "succE", .tcons "arrow" [.tcons "Odd" [], .tcons "Even" []] => EvenN.succE
  | "succO", .tcons "arrow" [.tcons "Even" [], .tcons "Odd" []] => OddN.succO
  | _, _ => default

/-- Every function of the factory is `zero`, `succE` or `succO`. -/
private theorem evenF_cases (f : LFunc TP) (hf : f ∈ evenF.toArray) :
    f = zeroEF ∨ f = succEF ∨ f = succOF := (mem_evenF f).mp hf

/-- Every datatype sort of the factory is `Even` or `Odd`. -/
private theorem evenF_isDatatypeSort_eq (s : LSort)
    (hs : evenF.IsDatatypeSort s) :
    s = .tcons "Even" [] ∨ s = .tcons "Odd" [] := by
  obtain ⟨f, hf, _, vt, hout⟩ := hs
  rw [← hout]
  rcases evenF_cases f hf with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The model satisfies disjointness, injectivity and induction. -/
private theorem evenConsistent :
    ConstrInterpConsistent evenTc evenOp evenF := by
  constructor
  · intro f1 f2 h1 h2 _ _ hne vt
    dsimp only
    intro heq args1 args2
    rcases evenF_cases f1 h1 with rfl | rfl | rfl <;>
      rcases evenF_cases f2 h2 with rfl | rfl | rfl
    · exact absurd rfl hne
    · change HList (SortDenote evenTc) [] at args1
      change HList (SortDenote evenTc) [.tcons "Odd" []] at args2
      cases args1
      rcases args2 with _ | ⟨o, args2⟩
      cases args2
      intro h
      change EvenN.zero = EvenN.succE o at h
      cases h
    · change LSort.tcons "Even" [] = LSort.tcons "Odd" [] at heq
      simp only [LSort.tcons.injEq] at heq
      exact absurd heq.1 (by decide)
    · change HList (SortDenote evenTc) [] at args2
      change HList (SortDenote evenTc) [.tcons "Odd" []] at args1
      cases args2
      rcases args1 with _ | ⟨o, args1⟩
      cases args1
      intro h
      change EvenN.succE o = EvenN.zero at h
      cases h
    · exact absurd rfl hne
    · change LSort.tcons "Even" [] = LSort.tcons "Odd" [] at heq
      simp only [LSort.tcons.injEq] at heq
      exact absurd heq.1 (by decide)
    · change LSort.tcons "Odd" [] = LSort.tcons "Even" [] at heq
      simp only [LSort.tcons.injEq] at heq
      exact absurd heq.1 (by decide)
    · change LSort.tcons "Odd" [] = LSort.tcons "Even" [] at heq
      simp only [LSort.tcons.injEq] at heq
      exact absurd heq.1 (by decide)
    · exact absurd rfl hne
  · intro f hf _ vt
    dsimp only
    intro args1 args2 h
    rcases evenF_cases f hf with rfl | rfl | rfl
    · change HList (SortDenote evenTc) [] at args1 args2
      cases args1
      cases args2
      rfl
    · change HList (SortDenote evenTc) [.tcons "Odd" []] at args1 args2
      rcases args1 with _ | ⟨o1, args1⟩
      rcases args2 with _ | ⟨o2, args2⟩
      cases args1
      cases args2
      change EvenN.succE o1 = EvenN.succE o2 at h
      have ho : o1 = o2 := EvenN.succE.inj h
      subst ho
      rfl
    · change HList (SortDenote evenTc) [.tcons "Even" []] at args1 args2
      rcases args1 with _ | ⟨e1, args1⟩
      rcases args2 with _ | ⟨e2, args2⟩
      cases args1
      cases args2
      change OddN.succO e1 = OddN.succO e2 at h
      have he : e1 = e2 := OddN.succO.inj h
      subst he
      rfl
  · intro P hstep s v hs
    have hzero : P (.tcons "Even" []) EvenN.zero :=
      hstep zeroEF ((mem_evenF zeroEF).mpr (Or.inl rfl)) rfl (fun _ => .bool)
        .nil trivial
    have hsuccE : ∀ o : OddN, P (.tcons "Odd" []) o →
        P (.tcons "Even" []) (EvenN.succE o) := by
      intro o ho
      exact hstep succEF ((mem_evenF succEF).mpr (Or.inr (Or.inl rfl))) rfl
        (fun _ => .bool) (.cons o .nil) ⟨fun _ => ho, trivial⟩
    have hsuccO : ∀ e : EvenN, P (.tcons "Even" []) e →
        P (.tcons "Odd" []) (OddN.succO e) := by
      intro e he
      exact hstep succOF ((mem_evenF succOF).mpr (Or.inr (Or.inr rfl))) rfl
        (fun _ => .bool) (.cons e .nil) ⟨fun _ => he, trivial⟩
    rcases evenF_isDatatypeSort_eq s hs with rfl | rfl
    · change EvenN at v
      exact EvenN.rec (motive_1 := fun e => P (.tcons "Even" []) e)
        (motive_2 := fun o => P (.tcons "Odd" []) o) hzero hsuccE hsuccO v
    · change OddN at v
      exact OddN.rec (motive_1 := fun e => P (.tcons "Even" []) e)
        (motive_2 := fun o => P (.tcons "Odd" []) o) hzero hsuccE hsuccO v

end Lambda
