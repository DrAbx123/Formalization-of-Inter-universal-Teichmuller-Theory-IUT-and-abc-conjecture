import tmp.sheaf.xif.paper.Mzk1StepXIScalingDirectionCandidateV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi scaling direction decision point

Decision point: the base point is always included in the corrected candidate, while
the original scaled region decomposes into the corrected candidate plus scaled pt. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingDecisionPointV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingDirectionCandidateActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_decision_point
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    pt ∈ scaledUnitWithBase T scale pt ∧
      tripleScaleRegion T scale pt =
        scale '' s1902UnitRegion T ∪ scale '' ({pt} : Set (S1902Carrier T)) :=
  ⟨scaledUnitWithBase_contains_pt T scale pt,
    tripleScaleRegion_eq_scaled_unit_union_scaled_pt T scale pt⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingDecisionPointV2Actual

end
