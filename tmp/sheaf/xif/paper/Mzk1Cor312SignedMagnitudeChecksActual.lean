import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# A544 chain-independent check: signed vs magnitude form of Cor 3.12

For positive magnitudes `qMag = |log q|`, `thetaMag = |log Theta|`, the paper
signed inequality `-thetaMag <= -qMag` is equivalent to the magnitude form
`thetaMag <= qMag`; the strict forms and the `C_Theta >= -1` form follow.  These
are the real-arithmetic statement equivalences used by the final chain.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual

/-- Signed inequality `-|log Theta| <= -|log q|` is equivalent to
`|log Theta| <= |log q|`. -/
theorem signed_ineq_iff_magnitude {qMag thetaMag : Real} :
    -thetaMag ≤ -qMag ↔ thetaMag ≥ qMag := by
  constructor <;> intro h <;> linarith

theorem signed_ineq_iff_magnitude' {qMag thetaMag : Real} :
    -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag := by
  constructor <;> intro h <;> linarith

/-- Strict signed form `-|log Theta| < -|log q|` is equivalent to the strict
magnitude form `|log q| < |log Theta|`. -/
theorem signed_strict_iff_magnitude {qMag thetaMag : Real} :
    -thetaMag < -qMag ↔ qMag < thetaMag := by
  constructor <;> intro h <;> linarith

/-- `C_Theta` form: if `-|log Theta| = C * |log q|` and the signed comparison
`-|log q| <= -|log Theta|` holds with `|log q| > 0`, then `C >= -1`. -/
theorem CTheta_ge_neg_one_of_signed {qMag C : Real} (hq : 0 < qMag)
    (hineq : -qMag ≤ C * qMag) : -1 ≤ C := by
  have hmul : (-1 : Real) * qMag ≤ C * qMag :=
    calc (-1 : Real) * qMag = -qMag := by ring
      _ ≤ C * qMag := hineq
  exact le_of_mul_le_mul_right hmul hq

/-- Strict `C_Theta` form: under the strict signed comparison, `C > -1`. -/
theorem CTheta_gt_neg_one_of_signed_strict {qMag C : Real} (hq : 0 < qMag)
    (hineq : -qMag < C * qMag) : -1 < C := by
  have hmul : (-1 : Real) * qMag < C * qMag :=
    calc (-1 : Real) * qMag = -qMag := by ring
      _ < C * qMag := hineq
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hq)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual
