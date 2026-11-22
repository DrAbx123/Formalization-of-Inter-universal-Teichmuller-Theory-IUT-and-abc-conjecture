/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaVConsumerChainActual
import Mathlib.Tactic

/-! # P7/#5: chain paper-V identification -> explicit normalized value -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVNormChainActual

open LeanFormal.IUT.XiFPaper.Mzk1ThetaVFactorInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaVConsumerChainActual

/-- Under the theta-V identification and `dim != 0`, the paper normalized value
is exactly `raw / dim`. -/
theorem paperV_eq_raw_div_dim {raw dim paperV : ℝ}
    (hdim : dim ≠ 0)
    (hident : ThetaVFactorIdentification raw dim paperV) :
    paperV = raw / dim := by
  have := paperV_eq_norm_of_identification (raw := raw) (dim := dim)
    (norm := raw / dim) (paperV := paperV) hdim hident rfl
  exact this

end LeanFormal.IUT.XiFPaper.Mzk1ThetaVNormChainActual