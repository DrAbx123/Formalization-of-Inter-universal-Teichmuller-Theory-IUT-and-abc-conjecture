/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Data.Real.Basic

/-! # A590: nonempty numeric witness for the Gap-2 named estimate `SNamed` -/

noncomputable section

namespace LeanFormal.IUT.Objects.ABCBridgeGap2Numeric

open LeanFormal.IUT.Objects.ABCBridgeGap2
open scoped ENNReal

/-- Concrete numeric instance: `l = 13`-side weight `log 11`, `eps = 1`, `theta = 0`,
`D = 0`, region volume taken at the boundary value `(1+eps)*w + theta + D`.
This is a genuine (non-True) inhabitant of `SNamed`, not a proof of the analytic estimate. -/
def witnessRegionVolume : ENNReal :=
  ENNReal.ofReal ((1 + (1 : ℝ)) * Real.log 11 + 0 + 0)

theorem witness_SNamed :
    SNamed witnessRegionVolume (1 : ℝ) (Real.log 11) 0 0 :=
  le_rfl

theorem witness_real_bound :
    witnessRegionVolume.toReal ≤ (1 + (1 : ℝ)) * Real.log 11 + 0 + 0 :=
  gap2_real_bound (by positivity) witness_SNamed

end LeanFormal.IUT.Objects.ABCBridgeGap2Numeric
