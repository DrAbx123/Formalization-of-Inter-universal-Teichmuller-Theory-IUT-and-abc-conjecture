import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1StepXITripleDependentScalingActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi triple-dependent region alignment

Region construction `scale '' (unitRegion ∪ {pt})` and its identity-scale
alignment with the literal unit region. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def tripleScaleRegion
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    Set (S1902Carrier T) :=
  scale '' (s1902UnitRegion T ∪ {pt})

theorem tripleScaleRegion_id (pt : S1902Carrier T) :
    tripleScaleRegion T id pt = s1902UnitRegion T ∪ {pt} := by
  simp [tripleScaleRegion]

theorem tripleScaleRegion_contains_scaled_unit
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    scale '' s1902UnitRegion T ⊆ tripleScaleRegion T scale pt := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, Or.inl hy, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

end
