import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi triple-scale obstruction

Obstruction: if the point is not in the range of the triple-dependent scale, it
cannot belong to the scaled region.  Also, the scaled region is contained in the
range of the scale. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionTripleScaleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem tripleScaleRegion_subset_range
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    tripleScaleRegion T scale pt ⊆ Set.range scale := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, rfl⟩

theorem not_mem_tripleScaleRegion_of_not_range
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T)
    (h : pt ∉ Set.range scale) :
    pt ∉ tripleScaleRegion T scale pt := by
  intro hx
  exact h (tripleScaleRegion_subset_range T scale pt hx)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIObstructionTripleScaleActual

end
