import tmp.sheaf.xif.paper.Mzk1P3NetGainSourceGapActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3R37NetActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainSourceGapActual
def r37Net (G h corrections : ℝ) : ℝ := netQuantity G h corrections
theorem r37Net_nonneg_iff (G h corrections : ℝ) :
    0 ≤ r37Net G h corrections ↔ 0 ≤ netQuantity G h corrections := Iff.rfl
theorem r37Net_eq_log_ratio {G massK massL massQ h corrections : ℝ}
    (hG : G = Real.log massK - Real.log massQ)
    (hh : h = Real.exp (Real.log massK - Real.log massL)) :
    r37Net G h corrections = Real.log massL - Real.log massQ + corrections := by
  unfold r37Net
  exact netQuantity_eq_sourceNetComparison hG hh
end LeanFormal.IUT.XiFPaper.Mzk1P3R37NetActual
end