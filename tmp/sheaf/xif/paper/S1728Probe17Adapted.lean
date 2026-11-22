import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe15c

open CategoryTheory

universe u

variable (D : Type (u + 1)) [Category.{u + 1, u + 1} D]

example (H : D → D → Type u)
    (e : ∀ A B, H A B ≃ (A ⟶ B)) :
    Category.{u, u + 1} D where
  Hom := H
  id A := (e A A).symm (𝟙 A)
  comp {A B C} f g := (e A C).symm ((e A B f) ≫ (e B C g))
  id_comp {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.id_comp (f := e A B f)
  comp_id {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.comp_id (f := e A B f)
  assoc {A B C E} f g h := by
    apply (e A E).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.assoc (f := e A B f) (g := e B C g) (h := e C E h)

end Probe15c
