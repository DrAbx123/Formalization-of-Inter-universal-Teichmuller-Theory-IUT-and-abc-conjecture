/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A759: dictionary cross-check — our geometric chain vs lana SSIneq -/

/- lana definitions (repo-root Iut/): QPilotData.logQ = sum_w weight_w * qOrder_w * log p_w
(Cor312/LeftHandSide.lean:81); absLogQ = logQ/(2*l) (:88); lhs = -absLogQ (:93);
nC D = (l-1)/2 (Wall/Rss.lean:303); sFactor n = (sum_{j<n}(j+1)^2)/n (Wall/Pilots.lean:55);
SSIneq D := (sFactor (nC D) - 1) * absLogQ <= logVol D (hullOf D (vcI D)) (Wall/MultiContainer.lean:88).

Our S1902 geometric chain gives logQ <= logVol(hullRegion) - logVol(unitRegion) (coefficient 1).
lana SSIneq coefficient is (sFactor(nC)-1)/(2l), e.g. l=13 (nC=6): sFactor 6 = 91/6,
coefficient = (91/6-1)/26 = 85/156 ≈ 0.5449.  So if the log-volumes were the same object,
our inequality would be ~1.83x stronger and would imply SSIneq.  But lana logVol is the
procession-normalized container volume (Wall/Rss.lean:324) and our volume is a product Haar
volume; no normalization bridge is proved, so the geometric chain does NOT prove SSIneq.
The missing bridge is: ourLogVol(fullRegion) vs lanaLogVol(hull(VC(I))) up to the 1/l* average
and theta-radius normalization. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PilotDictionaryCrosscheckActual

def absLogQOf (logQ l : ℝ) : ℝ := logQ / (2 * l)

def ssIneqScalarWithCoeff (c logQ hullVol : ℝ) : Prop := c * logQ ≤ hullVol

theorem mul_div_two_eq (s l logQ : ℝ) :
    (s - 1) * (logQ / (2 * l)) = ((s - 1) / (2 * l)) * logQ := by
  field_simp

theorem ssIneq_iff_coeff {s l logQ hullVol : ℝ} :
    (s - 1) * absLogQOf logQ l ≤ hullVol ↔
      ((s - 1) / (2 * l)) * logQ ≤ hullVol := by
  unfold absLogQOf
  rw [mul_div_two_eq]

theorem ssIneq_of_geometric_chain {c logQ H : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hq : 0 ≤ logQ) (hgeom : logQ ≤ H) : ssIneqScalarWithCoeff c logQ H := by
  unfold ssIneqScalarWithCoeff
  nlinarith

theorem coeff_l13_exact : ((91 : ℝ) / 6 - 1) / (2 * 13) = 85 / 156 := by
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1PilotDictionaryCrosscheckActual
