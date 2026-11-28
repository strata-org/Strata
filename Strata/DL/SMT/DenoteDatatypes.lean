/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Solver

/-! # A generic carrier for SMT datatypes

The denotation of SMT queries (`Strata.DL.SMT.Denote`) needs a Lean type for
every datatype sort. SMT-LIB datatypes are the free term algebra of their
constructors, so the type is fixed, unlike an uninterpreted sort, which the
denotation quantifies over. A definition cannot build one Lean inductive per
datatype, so all datatypes share one inductive `DVal P` of constructor
applications, and a datatype sort denotes the well-sorted values of that
inductive (`Carrier`). `P` is the type of non-datatype field payloads; in the
denotation it is a sigma over the denoted sorts.

This file has the carrier, well-sortedness against the SMT declarations, the
tester on it, the field a selector reads (`selField`), and the laws SMT assumes:
disjointness, injectivity, exhaustiveness, that fields of a well-sorted value are
well sorted, and that a selector reads back the argument its constructor was
given (`selField_mk`). The value of a selector on another constructor is given in
`Denote.lean`: an uninterpreted function the denotation quantifies over.

A declaration is looked up by name and the first match counts, for datatypes and
for constructors alike, in well-sortedness as in every operation. A second
declaration of a name is therefore never used. `Denote.denoteQuery` refuses
declarations that repeat a name, as SMT-LIB does.

The arguments of a value are a first-order list, so a field of function sort has
no representation. The encoder sends such a field as an SMT array, and
`Denote.denoteQuery` refuses its datatype (`dtFieldsDenotable`).
-/

public section

namespace Strata.SMT.DT

open Strata.SMT

mutual
/-- Constructor applications; a field is either a payload (any non-datatype sort)
or another datatype value. -/
inductive DVal (P : Type) : Type where
  | mk (ctor : String) (args : List (DArg P))
inductive DArg (P : Type) : Type where
  | prim (p : P)
  | dt (v : DVal P)
end

/-- The datatypes in scope: name, and constructors with field sorts. -/
abbrev Decls := List (String × List SMTConstructor)

/-- The constructors of datatype `d`: those of its first declaration. -/
@[expose] def ctorsOf (ds : Decls) (d : String) : Option (List SMTConstructor) :=
  (ds.find? (·.1 == d)).map (·.2)

/-- Is `d` a declared datatype? -/
@[expose] def declared (ds : Decls) (d : String) : Bool := (ctorsOf ds d).isSome

/-- Is `t` the sort of a declared datatype? -/
@[expose] def isDtSort (ds : Decls) : TermType → Option String
  | .constr d [] => if declared ds d then some d else none
  | _ => none

/-- The constructor of `cs` named `c`: the first one. -/
@[expose] def ctorNamed (cs : List SMTConstructor) (c : String) : Option SMTConstructor :=
  cs.find? (·.name == c)

/-- A payload has the sort it claims; the parameter decides this for the
denotation's own notion of sort. -/
structure Sorted (P : Type) where
  hasSort : P → TermType → Prop

mutual
/-- `v` is a value of datatype `d`. -/
inductive WS (ds : Decls) (S : Sorted P) : String → DVal P → Prop where
  | mk {d c args ctor cs} :
      ctorsOf ds d = some cs → ctorNamed cs c = some ctor →
      WSArgs ds S (ctor.args.map (·.2)) args → WS ds S d (.mk c args)
/-- The arguments match the field sorts, position by position. -/
inductive WSArgs (ds : Decls) (S : Sorted P) : List TermType → List (DArg P) → Prop where
  | nil : WSArgs ds S [] []
  | prim {t p ts as} : isDtSort ds t = none → S.hasSort p t →
      WSArgs ds S ts as → WSArgs ds S (t :: ts) (.prim p :: as)
  | dt {t d v ts as} : isDtSort ds t = some d → WS ds S d v →
      WSArgs ds S ts as → WSArgs ds S (t :: ts) (.dt v :: as)
end

/-- The denotation of datatype sort `d`. -/
abbrev Carrier (ds : Decls) (S : Sorted P) (d : String) : Type := { v : DVal P // WS ds S d v }

variable {P : Type} {ds : Decls} {S : Sorted P} {d : String}

/-- Constructor name of a value. -/
@[expose] def DVal.ctor : DVal P → String | .mk c _ => c
/-- Arguments of a value. -/
@[expose] def DVal.args : DVal P → List (DArg P) | .mk _ as => as

/-- Tester: `is-c`. -/
@[expose] def tester (c : String) (v : Carrier ds S d) : Prop := v.1.ctor = c

/-! ## Looking up declarations -/

theorem ctorNamed_name {cs : List SMTConstructor} {c : String} {ctor : SMTConstructor}
    (h : ctorNamed cs c = some ctor) : ctor.name = c := by
  simpa using List.find?_some h

theorem ctorNamed_mem {cs : List SMTConstructor} {c : String} {ctor : SMTConstructor}
    (h : ctorNamed cs c = some ctor) : ctor ∈ cs :=
  List.mem_of_find?_eq_some h

theorem ctorsOf_mem {ds : Decls} {d : String} {cs : List SMTConstructor}
    (h : ctorsOf ds d = some cs) : (d, cs) ∈ ds := by
  simp only [ctorsOf, Option.map_eq_some_iff] at h
  obtain ⟨⟨d', cs'⟩, hf, rfl⟩ := h
  have hd : d' = d := by simpa using List.find?_some hf
  exact hd ▸ List.mem_of_find?_eq_some hf

/-- A declared datatype has constructors to look up. -/
theorem ctorsOf_isSome_of_declared {ds : Decls} {d : String} (h : declared ds d = true) :
    (ctorsOf ds d).isSome := h

theorem declared_of_ctorsOf {ds : Decls} {d : String} {cs : List SMTConstructor}
    (h : ctorsOf ds d = some cs) : declared ds d = true := by
  simp [declared, h]

/-- A datatype sort is a declared name without arguments. -/
theorem isDtSort_eq_some {ds : Decls} {t : TermType} {d : String}
    (h : isDtSort ds t = some d) : t = .constr d [] ∧ declared ds d = true := by
  unfold isDtSort at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h
  · cases h

/-- With datatype names declared once, a declaration is the one its name finds. -/
theorem ctorsOf_of_mem {ds : Decls} {d : String} {cs : List SMTConstructor}
    (hnd : (ds.map (·.1)).Nodup) (h : (d, cs) ∈ ds) : ctorsOf ds d = some cs := by
  induction ds with
  | nil => cases h
  | cons e ds ih =>
    obtain ⟨d', cs'⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with heq | hm
    · cases heq; simp [ctorsOf]
    · have hne : d' ≠ d := fun hdd => hnd.1 (hdd ▸ List.mem_map_of_mem (f := (·.1)) hm)
      have := ih hnd.2 hm
      simpa [ctorsOf, List.find?_cons, hne] using this

/-- With constructor names declared once, a constructor is the one its name finds. -/
theorem ctorNamed_of_mem {cs : List SMTConstructor} {ctor : SMTConstructor}
    (hnd : (cs.map (·.name)).Nodup) (h : ctor ∈ cs) : ctorNamed cs ctor.name = some ctor := by
  induction cs with
  | nil => cases h
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with heq | hm
    · cases heq; simp [ctorNamed]
    · have hne : c.name ≠ ctor.name := fun hcc => hnd.1 (hcc ▸ List.mem_map_of_mem (f := (·.name)) hm)
      have := ih hnd.2 hm
      simpa [ctorNamed, List.find?_cons, hne] using this

/-! ## The laws SMT assumes -/

/-- Disjointness: a value is built by one constructor. -/
theorem disjoint {v : Carrier ds S d} {c c' : String} (h : tester c v) (h' : tester c' v) :
    c = c' := by
  simp only [tester] at h h'; exact h.symm.trans h'

/-- Injectivity: values built by the same constructor are equal only if their arguments
are. -/
theorem injective {c : String} {as bs : List (DArg P)}
    (h : (DVal.mk c as : DVal P) = DVal.mk c bs) : as = bs := by
  cases h; rfl

/-- The constructor of a value, read off `WS`: the value is built by a constructor of
`d`, and its arguments have that constructor's field sorts. -/
theorem WS.ctor_mem {v : DVal P} (h : WS ds S d v) :
    ∃ cs ctor, ctorsOf ds d = some cs ∧ ctorNamed cs v.ctor = some ctor ∧
      WSArgs ds S (ctor.args.map (·.2)) v.args := by
  cases h with
  | mk hd hc ha => exact ⟨_, _, hd, hc, ha⟩

/-- Exhaustiveness: a value of `d` is built by one of `d`'s constructors. -/
theorem exhaustive {v : Carrier ds S d} :
    ∃ cs ctor, (d, cs) ∈ ds ∧ ctor ∈ cs ∧ v.1.ctor = ctor.name := by
  obtain ⟨cs, ctor, hd, hc, _⟩ := v.2.ctor_mem
  exact ⟨cs, ctor, ctorsOf_mem hd, ctorNamed_mem hc, (ctorNamed_name hc).symm⟩

/-- The argument `a` is well sorted at sort `t`: a payload of the non-datatype sort `t`,
or a value of the datatype `t` names. -/
@[expose] def ArgWS (ds : Decls) (S : Sorted P) (t : TermType) : DArg P → Prop
  | .prim p => isDtSort ds t = none ∧ S.hasSort p t
  | .dt v => ∃ d, isDtSort ds t = some d ∧ WS ds S d v

/-- A field of a well-sorted value is itself well sorted at its declared sort. -/
theorem field_ws {ts : List TermType} {as : List (DArg P)} (h : WSArgs ds S ts as) :
    ∀ k (hk : k < as.length), ∃ t, ts[k]? = some t ∧ ArgWS ds S t as[k] :=
  match ts, as, h with
  | _, _, .nil => fun _ hk => by simp at hk
  | _, _, .prim hnd hs h' => fun k hk =>
    match k with
    | 0 => ⟨_, rfl, hnd, hs⟩
    | k + 1 => field_ws h' k (by simpa using hk)
  | _, _, .dt hd hv h' => fun k hk =>
    match k with
    | 0 => ⟨_, rfl, _, hd, hv⟩
    | k + 1 => field_ws h' k (by simpa using hk)
termination_by structural h

/-! ## Selectors -/

/-- The argument selector `sel` reads from `v`, with its declared sort: the field of
`v`'s own constructor that `sel` names. `none` if that constructor has no such field,
which is where SMT-LIB leaves the selector's value unspecified. -/
@[expose] def selField (cs : List SMTConstructor) (v : DVal P) (sel : String) :
    Option (DArg P × TermType) :=
  (ctorNamed cs v.ctor).bind fun ctor =>
    (ctor.args.findIdx? (·.1 == sel)).bind fun k =>
      (v.args[k]?).bind fun a => (ctor.args[k]?).map fun f => (a, f.2)

/-- The argument a selector reads is well sorted at the sort the selector declares. -/
theorem selField_ws {cs : List SMTConstructor} {v : DVal P} {sel : String} {a : DArg P}
    {t : TermType} (hv : WS ds S d v) (hd : ctorsOf ds d = some cs)
    (h : selField cs v sel = some (a, t)) : ArgWS ds S t a := by
  obtain ⟨cs', ctor, hd', hc, hargs⟩ := hv.ctor_mem
  obtain rfl : cs' = cs := Option.some.inj (hd'.symm.trans hd)
  simp only [selField, hc, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Prod.mk.injEq] at h
  obtain ⟨k, -, a', ha, f, hf, rfl, rfl⟩ := h
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨t, ht, hws⟩ := field_ws hargs k hk
  have : t = f.2 := by
    simp only [List.getElem?_map, hf, Option.map_some] at ht
    exact (Option.some.inj ht).symm
  exact this ▸ hws

/-- **A selector reads back what its constructor was given.** On a value built by
constructor `ctor` from the arguments `args`, the selector of `ctor`'s `k`-th field reads
the `k`-th argument. -/
theorem selField_mk {cs : List SMTConstructor} {ctor : SMTConstructor} {args : List (DArg P)}
    {sel : String} {k : Nat} {a : DArg P} {f : String × TermType}
    (hc : ctorNamed cs ctor.name = some ctor)
    (hk : ctor.args.findIdx? (·.1 == sel) = some k)
    (ha : args[k]? = some a) (hf : ctor.args[k]? = some f) :
    selField cs (.mk ctor.name args : DVal P) sel = some (a, f.2) := by
  simp [selField, DVal.ctor, DVal.args, hc, hk, ha, hf]

/-- The first field named `sel` among the constructors `cs`, with its sort: the sort a
selector application has. -/
@[expose] def findSel (cs : List SMTConstructor) (sel : String) :
    Option (SMTConstructor × Nat × TermType) :=
  cs.findSome? fun c =>
    (c.args.findIdx? (·.1 == sel)).bind fun k => (c.args[k]?).map fun f => (c, k, f.2)

end Strata.SMT.DT

end
