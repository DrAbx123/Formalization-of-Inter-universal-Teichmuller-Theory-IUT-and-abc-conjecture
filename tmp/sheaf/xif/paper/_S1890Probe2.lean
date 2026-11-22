import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory

namespace Probe2

-- abstract bicategory with IsLocallyDiscrete
example {B : Type} [Bicategory B] [IsLocallyDiscrete B] {C : Type} [Bicategory C]
    (obj : B → C) (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    map ((f ≫ g) ≫ h) = map (f ≫ (g ≫ h)) := by
  simp

example {B : Type} [Bicategory B] [IsLocallyDiscrete B] {C : Type} [Bicategory C]
    (obj : B → C) (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    map ((f ≫ g) ≫ h) = map (f ≫ (g ≫ h)) := by
  rw [obj_ext_of_isDiscrete (Strict.assoc f g h)]

end Probe2
