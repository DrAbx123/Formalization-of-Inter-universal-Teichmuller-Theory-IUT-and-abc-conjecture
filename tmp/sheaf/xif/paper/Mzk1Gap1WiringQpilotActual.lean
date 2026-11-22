/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperRegionScalingLawQpilotActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1Gap1WiringQpilotActual — Gap-1 wiring to the paper region scaling law (A664)

Wiring of the Gap-1 height comparison to the paper comparison-region scaling law:
the log form `log h ≤ log(1+ε) + log ratio + log base`, and its specialization to
the inverse-prime-power ratio `log h ≤ log(1+ε) + log base − ∑ e log f`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringQpilotActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual
open scoped BigOperators

/-- Gap-1 log form: `h ≤ (1+ε)v` with positive `h`,`v` gives
`log h ≤ log(1+ε) + log v`. -/
theorem gap1_log_form {h v epsilon : Real} (hh : 0 < h) (hv : 0 < v)
    (h1 : h ≤ (1 + epsilon) * v) :
    Real.log h ≤ Real.log (1 + epsilon) + Real.log v := by
  have hdiv : 0 < h / v := div_pos hh hv
  have hle : h / v ≤ 1 + epsilon := (div_le_iff₀ hv).mpr h1
  have hone : 0 < 1 + epsilon := lt_of_lt_of_le hdiv hle
  calc Real.log h ≤ Real.log ((1 + epsilon) * v) := Real.log_le_log hh h1
    _ = Real.log (1 + epsilon) + Real.log v := Real.log_mul (ne_of_gt hone) (ne_of_gt hv)

/-- Gap-1 log form wired to a paper region scaling law object. -/
theorem gap1_log_form_region {h epsilon : Real} (L : PaperRegionScalingLaw)
    (hh : 0 < h) (h1 : h ≤ (1 + epsilon) * L.regionVolume) :
    Real.log h ≤ Real.log (1 + epsilon) + Real.log L.ratio + Real.log L.base := by
  have hlog := gap1_log_form hh (paperRegion_volume_pos L) h1
  rw [paperRegion_log L] at hlog
  linarith

/-- Gap-1 inverse-product-ratio log form. -/
theorem gap1_log_form_invProd {ι : Type u} [Fintype ι] {h epsilon : Real}
    (L : PaperRegionScalingLaw) (f : ι → Real) (e : ι → Nat) (hf : ∀ i, 0 < f i)
    (hratio : L.ratio = ∏ i, (f i ^ e i)⁻¹)
    (hh : 0 < h) (h1 : h ≤ (1 + epsilon) * L.regionVolume) :
    Real.log h ≤ Real.log (1 + epsilon) + Real.log L.base -
      ∑ i, (e i : Real) * Real.log (f i) := by
  have hlog := gap1_log_form_region L hh h1
  have hratio_log : Real.log L.ratio = -∑ i, (e i : Real) * Real.log (f i) := by
    rw [hratio]
    exact log_prod_inv_pow f e hf
  linarith

/-- Rows for the Gap-1 wiring. -/
def gap1WiringRows : List (String × String) :=
  [ ("Gap1 log form", "PROVED"),
    ("Gap1 wired to region scaling law", "PROVED"),
    ("Gap1 inverse-product ratio log form", "PROVED") ]

theorem gap1WiringRows_length : gap1WiringRows.length = 3 := rfl

#check gap1_log_form
#check gap1_log_form_region
#check gap1_log_form_invProd
#check gap1WiringRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringQpilotActual
end
