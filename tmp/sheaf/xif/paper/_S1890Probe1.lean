import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory

namespace Probe1

variable {B₀ : Type} [Category B₀] {C : Type} [Bicategory C]

example (obj : B₀ → C) (map : ∀ {b b' : B₀}, (b ⟶ b') → (obj b ⟶ obj b'))
    {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    map ((f ≫ g) ≫ h) = map (f ≫ (g ≫ h)) := by
  simp

-- see what simp lemmas are used
example (obj : B₀ → C) (map : ∀ {b b' : B₀}, (b ⟶ b') → (obj b ⟶ obj b'))
    {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    map ((f ≫ g) ≫ h) = map (f ≫ (g ≫ h)) := by
  simp only [Category.assoc]

end Probe1
