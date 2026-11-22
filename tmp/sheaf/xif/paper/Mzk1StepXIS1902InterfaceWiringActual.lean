import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi S1902 interface wiring

Wires the concrete comparison region and hull-data alias to the green
`s1902IQHullLogVolumeInterface` fields. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902InterfaceWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902HullDataInstanceV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902ComparisonRegionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_wiring_imageSet :
    (stepxiS1902HullData T).imageSet = s1902ImageSet T := rfl

theorem stepxi_wiring_hull :
    (stepxiS1902HullData T).hull = s1902Hull T := rfl

theorem stepxi_wiring_comparisonRegion :
    (fun a b c => stepxiComparisonRegion T a b c) =
      (fun _ _ _ => s1902ImageSet T) := rfl

theorem stepxi_wiring_comparison_subset :
    ∀ a b c : Nat, stepxiComparisonRegion T a b c ⊆ (stepxiS1902HullData T).hull :=
  fun a b c => stepxiComparisonRegion_subset_hull T a b c

end LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902InterfaceWiringActual

end
