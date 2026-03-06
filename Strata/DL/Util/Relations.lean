/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
section Relation

def Relation (A: Type) := A → A → Prop
def Reflexive (r: Relation A) : Prop := ∀ x, r x x
def Transitive (r: Relation A) : Prop := ∀ x y z, r x y → r y z → r x z

inductive ReflTrans {A: Type} (r: Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step: ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z

theorem ReflTrans_Reflexive {A: Type} (r: Relation A):
  Reflexive (ReflTrans r) := by apply ReflTrans.refl

theorem ReflTrans_Transitive {A: Type} (r: Relation A):
  Transitive (ReflTrans r) := by
  unfold Transitive; intros x y z rxy
  induction rxy generalizing z
  case refl => simp
  case step x1 y1 z1 rxy1 ryz1 IH =>
    intros rzz1;
    apply (ReflTrans.step _ y1 _ rxy1 (IH _ rzz1))

end Relation
