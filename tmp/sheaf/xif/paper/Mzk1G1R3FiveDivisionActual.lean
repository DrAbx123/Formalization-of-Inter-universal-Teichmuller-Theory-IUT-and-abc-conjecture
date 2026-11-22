/- R3 (B)(C) first slice: degree/leading-coefficient/ne-zero data for the Legendre ψ₅.

  RECON: Mathlib DivisionPolynomial/Degree.lean:
  * `WeierstrassCurve.natDegree_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
      (W.preΨ n).natDegree = (n.natAbs ^ 2 - if Even n then 4 else 1) / 2`;
  * `WeierstrassCurve.leadingCoeff_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
      (W.preΨ n).leadingCoeff = if Even n then n / 2 else n`;
  * `WeierstrassCurve.preΨ_ne_zero [Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0)`.
  With n = 5 on the Legendre curve over ℂ: degree 12, leading coefficient 5, nonzero.
  These feed the (C) enumeration-count step (deg Ψ₅ = (5²-1)/2 = 12 => 12 x-roots,
  two y's each plus O => 25 = 5² candidates; the torsion CARDINALITY equality still needs
  the actual nsmul criterion, which is the (B) task).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTorsionFiveActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3FiveDivisionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionFiveActual

/-- Legendre `ψ₅` 非零（`preΨ_ne_zero`，n = 5）。 -/
theorem legendreΨ₅_ne_zero (lam : ℂ) : legendreΨ₅ lam ≠ 0 := by
  unfold legendreΨ₅ legendreΨn
  exact WeierstrassCurve.preΨ_ne_zero (W := legendreWeierstrassCurve lam) (n := 5)
    (by norm_num : ((5 : ℤ) : ℂ) ≠ 0)

/-- Legendre `ψ₅` 次数 = 12 = (5²−1)/2。 -/
theorem legendreΨ₅_natDegree (lam : ℂ) : (legendreΨ₅ lam).natDegree = 12 := by
  unfold legendreΨ₅ legendreΨn
  rw [WeierstrassCurve.natDegree_preΨ (W := legendreWeierstrassCurve lam) (n := 5)
    (by norm_num : ((5 : ℤ) : ℂ) ≠ 0)]
  norm_num

/-- Legendre `ψ₅` 首项系数 = 5。 -/
theorem legendreΨ₅_leadingCoeff (lam : ℂ) : (legendreΨ₅ lam).leadingCoeff = 5 := by
  unfold legendreΨ₅ legendreΨn
  rw [WeierstrassCurve.leadingCoeff_preΨ (W := legendreWeierstrassCurve lam) (n := 5)
    (by norm_num : ((5 : ℤ) : ℂ) ≠ 0)]
  norm_num

#print axioms legendreΨ₅_ne_zero
#print axioms legendreΨ₅_natDegree
#print axioms legendreΨ₅_leadingCoeff

end LeanFormal.IUT.XiFPaper.Mzk1G1R3FiveDivisionActual
