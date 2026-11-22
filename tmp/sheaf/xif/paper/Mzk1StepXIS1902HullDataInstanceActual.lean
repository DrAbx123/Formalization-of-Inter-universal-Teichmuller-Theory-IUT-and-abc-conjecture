import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi S1902 concrete hull-data instance

Concrete alias of the green `s1902IQHullLogVolumeInterface` with its field
equalities exposed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902HullDataInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def stepxiS1902HullData :
    IQHullLogVolumeInterface (S1902Carrier T) :=
  s1902IQHullLogVolumeInterface T

theorem stepxiS1902HullData_hull :
    stepxiS1902HullData T |>.hull = s1902Hull T := rfl

theorem stepxiS1902HullData_imageSet :
    stepxiS1902HullData T |>.imageSet = s1902ImageSet T := rfl

theorem stepxiS1902HullData_finite :
    stepxiS1902HullData T |>.logVolume (stepxiS1902HullData T |>.hull) < ⊤ :=
  stepxiS1902HullData T |>.hull_logVolume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902HullDataInstanceActual

end
