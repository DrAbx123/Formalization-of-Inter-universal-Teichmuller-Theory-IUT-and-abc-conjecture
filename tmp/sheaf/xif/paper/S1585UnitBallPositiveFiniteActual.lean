import tmp.sheaf.xif.paper.S1584ProductUnitBallScalingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1585UnitBallPositiveFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1576ProductHaarDecompositionActual
open LeanFormal.IUT.XiFPaper.S1584ProductUnitBallScalingActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.NumberFieldFinitePlace

variable (s : Finset (NumberField.FinitePlace ℚ))

/-- Exact first measure lemma: the dependent unit ball has positive finite
canonical Haar mass. -/
abbrev S1585UnitBallPositiveFinite : Prop :=
  S1584UnitBallPositiveFinite s

/-- Conditional actual: positive/finite unit ball plus S1584 product scaling
gives the dependent character identity. -/
theorem s1585DependentProductScalingChar_of_posFin
    (h : S1585UnitBallPositiveFinite s) :
    DependentProductScalingChar s :=
  s1584DependentProductScalingChar_of_posFin s h

/-- The unit ball is the coordinate product of local closed unit balls. -/
theorem s1585UnitRegion_eq_pi :
    dependentUnitRegion s =
      Set.univ.pi (fun v => Metric.closedBall (0 : S1402DependentE s v) 1) := by
  ext x
  simp [dependentUnitRegion, LocalFieldProductHull.unitRegion,
    Metric.mem_closedBall, dist_zero_right, Set.mem_pi]

end LeanFormal.IUT.XiFPaper.S1585UnitBallPositiveFiniteActual

end
