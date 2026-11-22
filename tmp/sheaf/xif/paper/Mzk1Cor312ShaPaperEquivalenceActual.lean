import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# shehdd A573: paper-form equivalences for Cor 3.12 (chain-independent)

Pure real-arithmetic checks used by the acceptance/ABC consumers:
* signed form `-|log Theta| <= -|log q|` <-> magnitude form `|log q| <= |log Theta|`;
* strict version;
* `C_Theta >= -1` from the signed comparison with `|log q| > 0`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ShaPaperEquivalenceActual

theorem signed_iff_magnitude {qMag thetaMag : Real} :
    -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag := by
  constructor <;> intro h <;> linarith

theorem signed_strict_iff_magnitude {qMag thetaMag : Real} :
    -thetaMag < -qMag ↔ qMag < thetaMag := by
  constructor <;> intro h <;> linarith

theorem CTheta_of_signed {qMag C : Real} (hq : 0 < qMag)
    (h : -qMag ≤ C * qMag) : -1 ≤ C := by
  have hm : (-1 : Real) * qMag ≤ C * qMag := by
    calc (-1 : Real) * qMag = -qMag := by ring
      _ ≤ C * qMag := h
  exact le_of_mul_le_mul_right hm hq

theorem CTheta_strict_of_signed {qMag C : Real} (hq : 0 < qMag)
    (h : -qMag < C * qMag) : -1 < C := by
  have hm : (-1 : Real) * qMag < C * qMag := by
    calc (-1 : Real) * qMag = -qMag := by ring
      _ < C * qMag := h
  exact lt_of_mul_lt_mul_right hm (le_of_lt hq)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ShaPaperEquivalenceActual
