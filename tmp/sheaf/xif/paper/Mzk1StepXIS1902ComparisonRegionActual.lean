import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi S1902 concrete comparison region

Concrete comparison region for the S1902 hull: the image set, with containment
and log-volume monotonicity exposed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902ComparisonRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def stepxiComparisonRegion (a b c : Nat) : Set (S1902Carrier T) :=
  s1902ImageSet T

theorem stepxiComparisonRegion_subset_hull (a b c : Nat) :
    stepxiComparisonRegion T a b c ⊆ s1902Hull T :=
  s1902ImageSet_subset_hull T

theorem stepxiComparisonRegion_logVolume_mono (a b c : Nat)
    {U V : Set (S1902Carrier T)} (hUV : U ⊆ V) :
    s1902LogVolume T U ≤ s1902LogVolume T V :=
  s1902LogVolume_mono T hUV

end LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902ComparisonRegionActual

end
