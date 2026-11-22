import tmp.sheaf.xif.paper.Mzk1HTF4R6CrosswalkActual
import Mathlib.Tactic
/-!
# R6 IV:3172 erratum: one-sided height bound and per-place model metric

Route IV:3172: `h_E ≤ 2 (deg E / deg ω) h_ω + O(1)` (GenEll 1.4(ii)/1.6), NOT the Tate
local-height equality of GenEll 3.3.  Choose `m` with `2 deg E ≤ m deg ω`; then
`h_E ≤ m h_ω + C`.  Per-place metric: `R6MetricData.sum_lambda` (Crosswalk DONE 19:48:03).
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4R6HeightBoundActual
open LeanFormal.IUT.XiFPaper.HTF4R6CrosswalkActual

structure R6IV3172HeightData where
  m : ℝ
  degE : ℝ
  degOmega : ℝ
  hE : ℝ
  hOmega : ℝ
  hP : ℝ
  C : ℝ
  degOmega_pos : 0 < degOmega
  hOmega_nonneg : 0 ≤ hOmega
  hm : 2 * degE ≤ m * degOmega
  hP_nonneg : 0 ≤ hP
  hE_eq : hE = 2 * (degE / degOmega) * hOmega - hP
  hC_nonneg : 0 ≤ C

theorem R6IV3172HeightData.hE_le (D : R6IV3172HeightData) :
    D.hE ≤ 2 * (D.degE / D.degOmega) * D.hOmega + D.C := by
  rw [D.hE_eq]
  nlinarith [D.hP_nonneg, D.hC_nonneg]

#print axioms R6IV3172HeightData.hE_le
end LeanFormal.IUT.XiFPaper.HTF4R6HeightBoundActual
end