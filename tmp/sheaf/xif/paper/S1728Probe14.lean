import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe15

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

-- We only need the quotient category from the previous probe; redeclare its
-- interface abstractly for the transport test.
variable (C : Type (u + 1)) [Category.{u + 1, u + 1} C]

example (H : C → C → Type u)
    (e : ∀ A B, H A B ≃ (A ⟶ B)) :
    Category.{u, u + 1} C where
  Hom := H
  id A := (e A A).symm (𝟙 A)
  comp {A B C} f g := (e A C).symm (@Category.comp C _ A B C (e A B f) (e B C g))
  id_comp {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact @Category.id_comp C _ A B (e A B f)
  comp_id {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact @Category.comp_id C _ A B (e A B f)
  assoc {A B C D} f g h := by
    apply (e A D).injective
    simp only [Equiv.apply_symm_apply]
    exact @Category.assoc C _ A B C D (e A B f) (e B C g) (e C D h)

end Probe15
