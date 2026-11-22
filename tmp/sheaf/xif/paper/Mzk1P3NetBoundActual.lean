import tmp.sheaf.xif.paper.Mzk1P3R37NetActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NetBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3R37NetActual
/-- Simple net bound: `net ≤ G + C` when `h ≥ 1`. -/
theorem r37Net_le_G_add (G h C : ℝ) (hh : 1 ≤ h) :
    r37Net G h C ≤ G + C := by
  unfold r37Net netQuantity
  have : 0 ≤ Real.log h := Real.log_nonneg hh
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P3NetBoundActual
end