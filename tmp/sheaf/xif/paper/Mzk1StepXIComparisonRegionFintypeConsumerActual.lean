import tmp.sheaf.xif.paper.Mzk1StepXIComparisonRegionMinimalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi minimal comparison region Fintype consumer

Consumer of the minimal comparison region with the explicit Fintype instance,
checking the downward closure and finiteness-facing data. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionFintypeConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionMinimalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_minimalRegion_fintype_subset (a b c : Nat) :
    minimalComparisonRegion T a b c ⊆ s1902Hull T :=
  minimalComparisonRegion_subset_hull T a b c

theorem stepxi_minimalRegion_fintype_mono (a b c : Nat)
    {U V : Set (S1902Carrier T)} (hUV : U ⊆ V) :
    s1902LogVolume T U ≤ s1902LogVolume T V :=
  minimalComparisonRegion_logVolume_mono T a b c hUV

end LeanFormal.IUT.XiFPaper.Mzk1StepXIComparisonRegionFintypeConsumerActual

end
