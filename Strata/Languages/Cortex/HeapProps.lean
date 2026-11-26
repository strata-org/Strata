/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LangDef
import all Strata.Languages.Cortex.Semantics

/-! # Properties of the relation's heap

The laws of a lawful heap API model (`HeapApiModel`) say nothing about which tags the
allocated objects of a heap have: a model's `Tag` may have values that are no class's tag,
and a heap of the model may hold objects allocated with them. The heaps a run of the relation
goes through have only the tags of classes (`WellTagged`): the heap a run starts from has it
by the initial-environment premise, and this file proves that allocation and field writes keep
it.

## Key results

- `not_holds_of_fails`: an API term that fails does not hold.
- `entryHeap_spec`: the heap a run starts from is a well-tagged heap.
- `wellTagged_newObj`: an allocation keeps a heap well tagged.
- `wellTagged_write`: a field write keeps a heap well tagged.
-/

namespace Cortex.Sem

open Imperative Lambda

public section

/-- A term that fails does not hold. -/
theorem not_holds_of_fails {f : Fac} {bs : List (String × SemValue)} {e : Expr}
    (hf : apiFails f bs e) : ¬ apiHolds f bs e := fun ht =>
  HasBool.ttVal_ne_ffVal (P := Core.Expression) f (Option.some.inj (ht.symm.trans hf))

/-- The heap a run starts from is a well-tagged heap. -/
theorem entryHeap_spec {Γ : UnorderedProgram} {params : Core.Logic.InitEnvWFParams} {fr : Frame}
    {ρ : Imperative.Env Core.Expression} (h : CortexInitEnvWF Γ params fr ρ) :
    IsOfTy ρ.factory (entryHeap ρ.factory ρ.store) heapTy ∧
      WellTagged Γ ρ.factory (entryHeap ρ.factory ρ.store) := by
  obtain ⟨v, hv, hty, hwt⟩ := h.entryHeap
  simp only [entryHeap, hv, Option.getD_some]
  exact ⟨hty, hwt⟩

/-- An allocation of a composite of `Γ` keeps a heap well tagged: the only new object has the
composite's tag. -/
theorem wellTagged_newObj {Γ : UnorderedProgram} {f : Fac} {h h' v : SemValue}
    {ty : TypeName} {cd : CompositeDecl} (hc : Γ.findComposite? ty = some cd)
    (hwt : WellTagged Γ f h) (hn : NewObj f h ty v h') : WellTagged Γ f h' := fun o ho ha => by
  obtain ⟨-, -, htag, hex, -, -⟩ := hn
  rcases hex o ho ha with hold | rfl
  · exact hwt o ho hold
  · have hc' : Γ.composites.find? (·.name == ty) = some cd := hc
    have hmem : cd ∈ Γ.composites := List.mem_of_find?_eq_some hc'
    have hname : cd.name = ty :=
      eq_of_beq (List.find?_some (p := fun c : CompositeDecl => c.name == ty) hc')
    subst hname
    exact ⟨cd, hmem, htag⟩

/-- A field write keeps a heap well tagged: it allocates nothing. -/
theorem wellTagged_write {Γ : UnorderedProgram} {f : Fac} (hm : HeapApiModel Γ f)
    {r : FieldRef} {d : FieldDecl} (hrd : (r, d) ∈ programFields Γ) {h o w h' : SemValue}
    (hh : IsOfTy f h heapTy) (ho : IsOfTy f o refTy) (hw : IsOfTy f w (fieldMonoTy Γ d))
    (hwr : apiEval f [("$h", h), ("$o", o), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h')
    (hwt : WellTagged Γ f h) : WellTagged Γ f h' := fun p hp ha =>
  hwt p hp ((hm.writeKeepsAllocated r d hrd h o w h' p hh ho hw hp hwr).symm.trans ha)

end -- public section

end Cortex.Sem
