import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2827SG3bProductHaarActual

universe u v

/-- Exact product-Haar formula on a finite Cartesian product: the Haar mass of
a product region is the product of the local masses. -/
theorem S2827_pi_pi {J : Type u} [Fintype J] {E : J -> Type v}
    [forall j, MeasurableSpace (E j)]
    (mu : (j : J) -> Measure (E j)) [forall j, SigmaFinite (mu j)]
    (S : (j : J) -> Set (E j)) :
    Measure.pi mu (Set.pi Set.univ S) = ∏ j, mu j (S j) :=
  Measure.pi_pi mu S

/-- Log form of the product-Haar formula; this is the exact product formula on
the product side. -/
theorem S2827_pi_pi_logVolume {J : Type u} [Fintype J] {E : J -> Type v}
    [forall j, MeasurableSpace (E j)]
    (mu : (j : J) -> Measure (E j)) [forall j, SigmaFinite (mu j)]
    (S : (j : J) -> Set (E j))
    (hpos : forall j, 0 < mu j (S j))
    (hfin : forall j, mu j (S j) < ⊤) :
    Real.log ((Measure.pi mu (Set.pi Set.univ S)).toReal) =
      ∑ j, Real.log ((mu j (S j)).toReal) := by
  rw [S2827_pi_pi]
  rw [ENNReal.toReal_prod]
  rw [Real.log_prod]
  intro j _
  exact (ENNReal.toReal_pos (hpos j).ne' (hfin j).ne).ne'

/-- The missing tensor-side identification: a field-product decomposition of
the C3 tensor block sends the tensor log-shell region to a Cartesian product
of local regions.  Stated abstractly; not asserted here. -/
def S2827TensorRegionProductImage {X Y : Type} (e : X ≃ Y)
    (region : Set X) (localRegion : Set Y) : Prop :=
  e '' region = localRegion

#check S2827_pi_pi
#check S2827_pi_pi_logVolume
#check S2827TensorRegionProductImage
#print axioms S2827_pi_pi_logVolume

end LeanFormal.IUT.XiFPaper.S2827SG3bProductHaarActual
end
