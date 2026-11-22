import tmp.sheaf.xif.paper.Mzk1P7TransvectionLargeImageActual
import tmp.sheaf.xif.paper.Mzk1S1PrimeAvoidanceActual
import tmp.sheaf.xif.paper.Mzk1S1IsogenyHeightActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1S1PrimeAvoidanceActual
open LeanFormal.IUT.XiFPaper.Mzk1S1IsogenyHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual

/-- Actual P7 large-image/cyclic-isogeny data assembled from the compiled
transvection step, the actual archimedean height-magnification data, and the
actual prime-avoidance window. -/
structure P7LargeImageCyclicData (c : ℝ) where
  archHeight : S1IsogenyHeightData c
  primeAvoidance : S1PrimeAvoidanceWindowData

def p7LargeImageCyclicData (c : ℝ) : P7LargeImageCyclicData c where
  archHeight := s1IsogenyHeightActual c
  primeAvoidance := s1PrimeAvoidanceWindowActual

theorem p7_archHeight_nonempty (c : ℝ) :
    Nonempty (S1IsogenyHeightData c) :=
  ⟨s1IsogenyHeightActual c⟩

theorem p7_primeAvoidance_nonempty :
    Nonempty S1PrimeAvoidanceWindowData :=
  ⟨s1PrimeAvoidanceWindowActual⟩

/-- Actual transvection-to-SL2 step (restated from the compiled file). -/
theorem p7_sl2_of_transvection {F : Type*} [Field F] {l : PrimeGeFive}
    (X : PuncturedEllipticCurve F)
    (b : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)
    (hT : ∃ T : GL (Fin 2) (ZMod l.value),
      T ∈ (X.galoisLTorsionMatrixRepresentation l b).range ∧ T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0)
    (hline : ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ (X.galoisLTorsionMatrixRepresentation l b).range,
        ∀ c : ZMod l.value,
          Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) v ≠ c • v)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    A.toGL ∈ (X.galoisLTorsionMatrixRepresentation l b).range :=
  p7_sl2_le_range_of_transvection X b hT hline A

#print axioms p7LargeImageCyclicData
#print axioms p7_sl2_of_transvection
end LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageCyclicActual