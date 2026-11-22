import tmp.sheaf.xif.paper.Mzk1P3NetGainLogActual
/-! P3 (R3.7): exact source comparison interface and nonnegativity boundary. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NetGainSourceGapActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
/-- Exact missing source input for (R3.7): the corrected log mass ratio is nonnegative. -/
def sourceNetComparison (massL massQ corrections : ℝ) : Prop :=
  0 ≤ Real.log massL - Real.log massQ + corrections
/-- After substituting the root gain and the exact index, the net quantity is the
corrected log mass ratio of the smaller lattice vs the root. -/
theorem netQuantity_eq_sourceNetComparison
    {G massK massL massQ h corrections : ℝ}
    (hG : G = Real.log massK - Real.log massQ)
    (hh : h = Real.exp (Real.log massK - Real.log massL)) :
    netQuantity G h corrections = Real.log massL - Real.log massQ + corrections := by
  unfold netQuantity
  rw [hG, hh, Real.log_exp]
  ring
/-- Net nonnegativity is exactly `sourceNetComparison`. -/
theorem netQuantity_nonneg_iff_sourceNetComparison
    {G massK massL massQ h corrections : ℝ}
    (hG : G = Real.log massK - Real.log massQ)
    (hh : h = Real.exp (Real.log massK - Real.log massL)) :
    0 ≤ netQuantity G h corrections ↔ sourceNetComparison massL massQ corrections := by
  rw [netQuantity_eq_sourceNetComparison hG hh]
  unfold sourceNetComparison
  rfl
/-- Without source conditions the net quantity can be negative (not provable unconditionally). -/
theorem netQuantity_negative_without_source :
    netQuantity 0 2 0 < 0 := by
  unfold netQuantity
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num
  linarith
/-- Named missing item: no proof of `sourceNetComparison` from core data. -/
def missingSourceComparisonReason : String :=
  "R3.7 requires actual source comparison mass(L_H) >= mass(Q) after corrections; core gives the identity but not nonnegativity."
end LeanFormal.IUT.XiFPaper.Mzk1P3NetGainSourceGapActual
end