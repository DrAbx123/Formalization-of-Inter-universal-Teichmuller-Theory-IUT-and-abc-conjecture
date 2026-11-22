import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual

/-! # Mzk1Stage4ScalingElementAuditActual (stage4 lane; scaling element audit)

A657 module: audit of the canonical SCALING ELEMENT `tripleScale` (mainline file only
READ): its multiplier is positive, and at `(0,0,0)` it is the identity element.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingElementAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The scaling multiplier is positive. -/
theorem tripleScale_factor_pos (a b c : Nat) : 0 < a + b + c + 1 :=
  Nat.succ_pos _

/-- The scaling element at `(0,0,0)` is the identity element (the `scaleShift = id`
case). -/
theorem tripleScale_zero_apply (x : S1902Carrier T) :
    tripleScale T 0 0 0 x = x := by
  funext v
  simp [tripleScale]

/-- At `(0,0,0)` the comparison region is the un-scaled region `unit ∪ {pt}`. -/
theorem paperComparisonRegion_zero (point : Nat → Nat → Nat → S1902Carrier T) :
    paperComparisonRegion T point 0 0 0 = s1902UnitRegion T ∪ {point 0 0 0} := by
  simp only [paperComparisonRegion, tripleScale_zero_apply]
  exact Set.image_id _

#check tripleScale_factor_pos
#check tripleScale_zero_apply
#check paperComparisonRegion_zero

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ScalingElementAuditActual
end
