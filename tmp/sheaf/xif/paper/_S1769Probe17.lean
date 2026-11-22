import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev bc (K : Type) [Field K] : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

variable {K : Type} [Field K]

example : PreservesLimitsOfShape WalkingCospan (bc K).op ↔ PreservesColimitsOfShape WalkingSpan (bc K) := by
  constructor
  · intro h
    haveI := h
    haveI h1 : PreservesColimitsOfShape (WalkingCospan)ᵒᵖ (bc K) :=
      preservesColimitsOfShape_of_op (F := bc K) (J := WalkingCospan)
    exact preservesColimitsOfShape_of_equiv walkingCospanOpEquiv (bc K)
  · intro h
    haveI := h
    haveI h1 : PreservesColimitsOfShape (WalkingCospan)ᵒᵖ (bc K) :=
      preservesColimitsOfShape_of_equiv walkingCospanOpEquiv.symm (bc K)
    exact preservesLimitsOfShape_op (F := bc K) (J := WalkingCospan)

end S1769Probe