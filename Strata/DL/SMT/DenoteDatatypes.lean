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
tester and selector on it, and the laws SMT assumes: disjointness,
injectivity, exhaustiveness, and that fields of a well-sorted value are well
sorted. A selector applied to another constructor is unspecified in SMT-LIB, so
`selectorArg` takes that value from a parameter, which the denotation
quantifies over.
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

/-- Is `t` the sort of a declared datatype? -/
@[expose] def isDtSort (ds : Decls) : TermType → Option String
  | .constr d [] => if ds.any (·.1 == d) then some d else none
  | _ => none

/-- A payload has the sort it claims; the parameter decides this for the
denotation's own notion of sort. -/
structure Sorted (P : Type) where
  hasSort : P → TermType → Prop

mutual
/-- `v` is a value of datatype `d`. -/
inductive WS (ds : Decls) (S : Sorted P) : String → DVal P → Prop where
  | mk {d c args fields cs} :
      (d, cs) ∈ ds → ⟨c, fields⟩ ∈ cs →
      WSArgs ds S (fields.map (·.2)) args → WS ds S d (.mk c args)
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
@[expose] def DVal.args : DVal P → List (DArg P) | .mk _ as => as

/-- Tester: `is-c`. -/
@[expose] def tester (c : String) (v : Carrier ds S d) : Prop := v.1.ctor = c

/-- Selector of field `k` of constructor `c`, with `dflt` for the other
constructors: SMT-LIB leaves that case unspecified, so the denotation takes the
value from a parameter that `denoteQuery` quantifies over. -/
@[expose] def selectorArg (c : String) (k : Nat) (dflt : DArg P) (v : Carrier ds S d) : DArg P :=
  if v.1.ctor = c then (v.1.args.getD k dflt) else dflt

/-! ## The laws SMT assumes -/

theorem disjoint {v : Carrier ds S d} {c c' : String} (h : tester c v) (h' : tester c' v) :
    c = c' := by
  simp only [tester] at h h'; exact h.symm.trans h'

theorem injective {c : String} {as bs : List (DArg P)}
    (h : (DVal.mk c as : DVal P) = DVal.mk c bs) : as = bs := by
  cases h; rfl

/-- Exhaustiveness: a value of `d` is built by one of `d`'s constructors. -/
theorem exhaustive {v : Carrier ds S d} :
    ∃ cs c fields, (d, cs) ∈ ds ∧ (⟨c, fields⟩ : SMTConstructor) ∈ cs ∧ v.1.ctor = c := by
  obtain ⟨_, hv⟩ := v
  cases hv with
  | mk hd hc _ => exact ⟨_, _, _, hd, hc, rfl⟩

/-- A field of a well-sorted value is itself well sorted at its declared sort. -/
theorem field_ws {ts : List TermType} {as : List (DArg P)} (h : WSArgs ds S ts as) :
    ∀ k (hk : k < as.length), ∃ t, ts[k]? = some t ∧
      (match as[k] with
       | .prim p => isDtSort ds t = none ∧ S.hasSort p t
       | .dt v => ∃ d, isDtSort ds t = some d ∧ WS ds S d v) :=
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

/-! ## Looking up declarations -/

/-- The constructor, field index and field sort of selector `sel` in `cs`. -/
@[expose] def findSel (cs : List SMTConstructor) (sel : String) :
    Option (SMTConstructor × Nat × TermType) :=
  cs.findSome? fun c =>
    (c.args.findIdx? (·.1 == sel)).bind fun k => (c.args[k]?).map fun f => (c, k, f.2)

/-- The constructor of a value, read off `WS`: the value is built by a declared
constructor of `d`. -/
theorem WS.ctor_mem {v : DVal P} (h : WS ds S d v) :
    ∃ cs c fields, (d, cs) ∈ ds ∧ (⟨c, fields⟩ : SMTConstructor) ∈ cs ∧ v.ctor = c ∧
      WSArgs ds S (fields.map (·.2)) v.args := by
  cases h with
  | mk hd hc ha => exact ⟨_, _, _, hd, hc, rfl, ha⟩

/-! ## Sanity: `nat` as `pos`/`nat`, as Boole declares them -/

@[expose] def posNat : Decls :=
  [ ("pos", [⟨"xH", []⟩, ⟨"xO", [("pos..p", .constr "pos" [])]⟩, ⟨"xI", [("pos..p", .constr "pos" [])]⟩]),
    ("nat", [⟨"N0", []⟩, ⟨"Npos", [("nat..p", .constr "pos" [])]⟩]) ]

abbrev noPayload : Sorted Empty := ⟨fun p _ => p.elim⟩

@[expose] def xH : Carrier posNat noPayload "pos" :=
  ⟨.mk "xH" [], .mk (.head _) (.head _) .nil⟩
@[expose] def xO (p : Carrier posNat noPayload "pos") : Carrier posNat noPayload "pos" :=
  ⟨.mk "xO" [.dt p.1], .mk (.head _) (.tail _ (.head _)) (.dt rfl p.2 .nil)⟩
@[expose] def N0 : Carrier posNat noPayload "nat" :=
  ⟨.mk "N0" [], .mk (.tail _ (.head _)) (.head _) .nil⟩
@[expose] def Npos (p : Carrier posNat noPayload "pos") : Carrier posNat noPayload "nat" :=
  ⟨.mk "Npos" [.dt p.1], .mk (.tail _ (.head _)) (.tail _ (.head _)) (.dt rfl p.2 .nil)⟩

example : tester "xO" (xO xH) := rfl
example : ¬ tester "xH" (xO xH) := by simp [tester, xO, DVal.ctor]
example : selectorArg "xO" 0 (.dt xH.1) (xO xH) = .dt xH.1 := rfl

end Strata.SMT.DT

end
