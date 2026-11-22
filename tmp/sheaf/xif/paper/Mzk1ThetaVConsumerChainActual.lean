/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaVFactorInterfaceActual
import tmp.sheaf.xif.paper.Mzk1PacketNormalizedBoundActual
import Mathlib.Tactic

/-! # P7/#5: consumer chain raw = dim*paperV and norm = raw/dim -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVConsumerChainActual

open LeanFormal.IUT.XiFPaper.Mzk1ThetaVFactorInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedBoundActual

/-- Under the theta-V identification, the candidate normalized value equals the
paper normalized value when `dim ≠ 0`. -/
theorem paperV_eq_norm_of_identification {raw dim norm paperV : ℝ}
    (hdim : dim ≠ 0)
    (hident : ThetaVFactorIdentification raw dim paperV)
    (hnorm : norm = raw / dim) : paperV = norm := by
  unfold ThetaVFactorIdentification at hident
  have hraw : raw = dim * norm := raw_eq_dim_mul_of_norm_eq_div hdim hnorm
  have h : dim * paperV = dim * norm := by
    rw [← hident, hraw]
  exact mul_left_cancel₀ hdim h

/-- Conversely, if the paper normalized value is `raw/dim`, the identification holds. -/
theorem identification_of_paperV_eq_div {raw dim paperV : ℝ}
    (hdim : dim ≠ 0) (h : paperV = raw / dim) :
    ThetaVFactorIdentification raw dim paperV := by
  unfold ThetaVFactorIdentification
  rw [h]
  field_simp

end LeanFormal.IUT.XiFPaper.Mzk1ThetaVConsumerChainActual