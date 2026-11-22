import tmp.sheaf.xif.paper.Mzk1StepXITripleScaleRegionAlignmentActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi scaling direction correction candidate

Correction candidate for the A618 obstruction: add the base point `pt` directly to
the scaled region (instead of scaling `pt`).  The original region is recovered as
the corrected region together with the scaled point. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingDirectionCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXITripleScaleRegionAlignmentActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Corrected candidate: scaled unit region plus the base point. -/
noncomputable def scaledUnitWithBase
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    Set (S1902Carrier T) :=
  scale '' s1902UnitRegion T ∪ {pt}

theorem scaledUnitWithBase_contains_pt
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    pt ∈ scaledUnitWithBase T scale pt :=
  Or.inr (by simp)

theorem tripleScaleRegion_eq_corrected_union
    (scale : S1902Carrier T → S1902Carrier T) (pt : S1902Carrier T) :
    tripleScaleRegion T scale pt =
      scaledUnitWithBase T scale pt ∪ scale '' ({pt} : Set (S1902Carrier T)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · exact Or.inl (Or.inl ⟨y, hy, rfl⟩)
    · exact Or.inr ⟨y, hy, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨y, hy, rfl⟩ | hx
      · exact ⟨y, Or.inl hy, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨y, Or.inr rfl, rfl⟩
    · rcases hx with ⟨y, hy, rfl⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨y, Or.inr rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingDirectionCandidateActual

end
