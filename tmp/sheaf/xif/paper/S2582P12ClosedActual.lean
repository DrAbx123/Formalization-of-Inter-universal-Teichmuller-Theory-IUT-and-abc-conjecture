import tmp.sheaf.xif.paper.S2580P12CertificateActual
import tmp.sheaf.xif.paper.S2581PrimitiveThetaActual
import tmp.sheaf.xif.paper.S2005FprimeGroupActual
noncomputable section
set_option maxHeartbeats 16000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2580P12CertificateActual
open LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual
theorem S2582_P12Certificate : S2579P12Certificate := by
  apply S2580_certificate_iff.mpr
  let θ : S1720Field := S2579Theta
  have hint : IsIntegral ℚ θ := IsIntegral.of_finite ℚ θ
  have hfin := IntermediateField.adjoin.finrank hint
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ ({θ} : Set S1720Field)) = 12 := by
    rw [show IntermediateField.adjoin ℚ ({θ} : Set S1720Field) = ⊤ from S2581_primitive]
    simpa using S2005_finrank
  rw [← S2580_minpoly_rat_natDegree]
  rw [← hfin]
  exact hfr
#print axioms S2582_P12Certificate
end LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
end
