import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Limits

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

/-- test: empty scheme over a base, left projection -/
def TestEmptyOver (F : Type) [CommRing F] : Over (Spec (CommRingCat.of F)) :=
  Over.mk (Scheme.emptyTo (Spec (CommRingCat.of F)))

example (F : Type) [CommRing F] : (TestEmptyOver F).left = (∅ : Scheme) := rfl

example (F : Type) [CommRing F] : IsEmpty (TestEmptyOver F).left := by
  rw [show (TestEmptyOver F).left = (∅ : Scheme) from rfl]
  infer_instance

-- homMk with subsingleton proof
example (F : Type) [CommRing F] (V : Over (Spec (CommRingCat.of F))) :
    TestEmptyOver F ⟶ V :=
  Over.homMk (Scheme.emptyTo V.left) (Subsingleton.elim _ _)

example (F : Type) [CommRing F] (V : Over (Spec (CommRingCat.of F))) :
    Subsingleton (TestEmptyOver F ⟶ V) :=
  ⟨fun a b => Over.OverMorphismExt (Subsingleton.elim _ _)⟩

-- bottom presieve elimination
example {C : Type} [Category C] {X : C} :
    Presieve.FamilyOfElements (yoneda.obj X) (⊥ : Presieve X) :=
  fun _ _ hf => (hf : (⊥ : Presieve X) _).elim

example {C : Type} [Category C] {X : C} :
    (default : Presieve.FamilyOfElements (yoneda.obj X) (⊥ : Presieve X)).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
  exact (h₁ : (⊥ : Presieve X) f₁).elim

-- the bottom sieve's arrows are the bottom presieve
example {C : Type} [Category C] {X : C} (f : X ⟶ X) :
    ((⊥ : Sieve X) : Presieve X) f = (⊥ : Presieve X) f := rfl

end
