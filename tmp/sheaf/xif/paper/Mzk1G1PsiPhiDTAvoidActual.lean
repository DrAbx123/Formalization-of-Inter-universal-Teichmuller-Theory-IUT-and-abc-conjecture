/- B1 value layer: the value of `h(u)` at a protected point equals the constant `h(0)`
modulo the prime (route B1/B2 L240-280). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiPhiDTActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

/-- The protected image value, expressed as the image of the constant `h(0)`. -/
theorem phiFixedL_DT_value {n : Nat} {T : Finset ℚ}
    (P : Ideal (R n)) (hu : psiChart0Coord n T ∈ P) (h : Polynomial ℚ) :
    Ideal.Quotient.mk P (Polynomial.aeval (psiChart0Coord n T) h) =
      Ideal.Quotient.mk P (algebraMap ℚ (R n) (Polynomial.eval 0 h)) :=
  phiFixedL_chart0_value_eq_at_DT P hu h

#print axioms phiFixedL_DT_value
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTAvoidActual
-- t
