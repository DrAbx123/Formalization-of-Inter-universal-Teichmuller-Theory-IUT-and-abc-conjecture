import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

noncomputable section
open CategoryTheory Limits
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2525FiniteEtalePreGaloisAlgebra

universe u

variable (R : Type u) [CommRing R]

noncomputable instance S2525HasInitial : HasInitial (CommAlgCat.FiniteEtale.{u} R) := by
  refine @hasInitial_of_unique (CommAlgCat.FiniteEtale.{u} R) inferInstance (CommAlgCat.FiniteEtale.of (R := R) (S := R)) ?_ ?_
  · intro Y
    exact ⟨CommAlgCat.FiniteEtale.ofHom (Algebra.ofId R Y.obj)⟩
  · intro Y
    exact ⟨fun f g => by
      apply ObjectProperty.hom_ext
      ext⟩

#check S2525HasInitial
#print axioms S2525HasInitial
end LeanFormal.IUT.XiFPaper.S2525FiniteEtalePreGaloisAlgebra
end