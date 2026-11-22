
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual

namespace S2223Probe

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem kernel_fixes_lTorsion
    (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] T.arithmetic.curve.LTorsion l)
    (σ : AlgebraicClosure T.arithmetic.F ≃ₐ[T.arithmetic.F] AlgebraicClosure T.arithmetic.F)
    (hσ : σ ∈ (T.arithmetic.curve.galoisLTorsionKernelField l basis).fixingSubgroup)
    (P : T.arithmetic.curve.LTorsion l) :
    T.arithmetic.curve.galoisActionOnPoint σ (P : T.arithmetic.curve.AlgebraicClosurePoint) = P := by
  have hfix := T.arithmetic.curve.galoisLTorsionKernelField_fixingSubgroup l basis
  have hker : σ ∈ PuncturedEllipticCurve.galoisLTorsionKernelSubgroup l T.arithmetic.curve basis := by
    rw [← hfix]
    exact hσ
  have hmat : T.arithmetic.curve.galoisLTorsionMatrixRepresentation l basis σ = 1 := hker
  obtain ⟨c, hc⟩ := (basis.surjective P)
  have hacts := T.arithmetic.curve.galoisLTorsionMatrixRepresentation_acts l basis σ c
  rw [hmat] at hacts
  simp only [Matrix.GeneralLinearGroup.toLin] at hacts
  simpa [hc] using hacts.symm

end S2223Probe
end
