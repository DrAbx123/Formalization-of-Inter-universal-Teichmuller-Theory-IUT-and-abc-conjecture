import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison
import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1D1D3DonorProbeActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1QHeightActual

/-!
# One-round mapping probe: accepted ABCBridge donors for L-H D3 / D1

Checks that the accepted layer's actual Legendre-curve j-height bounds can be
consumed by the local lane's D3 shape
`|jHeight - 6 * lambdaHeight| <= B` for rational points, with an explicit
constant, and prints the axioms of the donors.
-/

/-- The local lane's Legendre j-function is the actual Mathlib j-invariant of
the Legendre Weierstrass model at the same parameter. -/
theorem legendreJ_eq_legendreCurve_j (p : ℚ) [(legendreWeierstrassCurve p).IsElliptic] :
    legendreJ p = (legendreWeierstrassCurve p).j := by
  rw [legendreWeierstrassCurve_j]
  unfold legendreJ
  have h : (1 - p + p ^ 2) ^ 3 = (p ^ 2 - p + 1) ^ 3 := by ring
  rw [h]

/-- **Direct donor for D3 (rational case).**  From the accepted actual
Legendre j-height bounds, the D3 height-dictionary shape holds at the ABC
rational point with the explicit constant `log 256`. -/
theorem d3_rat_of_abcTriple {a b c : ℕ} (h : IsABCTriple a b c) :
    |jHeight (abcRationalPoint a c) - 6 * lambdaHeight (abcRationalPoint a c)|
      ≤ Real.log 256 := by
  letI := abcRationalPoint_legendre_isElliptic h
  have hb := abcRationalPoint_legendre_j_height_bounds h
  have hformula : legendreJ (abcRationalPoint a c) =
      (legendreWeierstrassCurve (abcRationalPoint a c)).j :=
    legendreJ_eq_legendreCurve_j (abcRationalPoint a c)
  have hH : jHeight (abcRationalPoint a c) =
      Height.logHeight₁ (legendreWeierstrassCurve (abcRationalPoint a c)).j := by
    rw [jHeight, hformula]
  have hL : lambdaHeight (abcRationalPoint a c) =
      Height.logHeight₁ (abcRationalPoint a c) := rfl
  rw [hH, hL, abs_le]
  have hupper := hb.2.2
  have hlower := hb.2.1
  constructor
  · have hlog : Real.log (64 / 27 : ℝ) = -Real.log (27 / 64 : ℝ) := by
      have hinv : ((27 / 64 : ℝ))⁻¹ = 64 / 27 := by norm_num
      rw [← hinv, Real.log_inv]
    have hmono : Real.log (64 / 27 : ℝ) ≤ Real.log 256 :=
      Real.log_le_log (by norm_num) (by norm_num)
    linarith
  · linarith

#print axioms legendreWeierstrassCurve_j
#print axioms abcRationalPoint_legendre_j_eq_abcJInvariant
#print axioms abcRationalPoint_legendre_j_height_bounds
#print axioms abcJInvariant_logHeight_bounds_abcRationalPoint
#print axioms legendreJ_eq_legendreCurve_j
#print axioms d3_rat_of_abcTriple

end LeanFormal.IUT.XiFPaper.Mzk1D1D3DonorProbeActual
end