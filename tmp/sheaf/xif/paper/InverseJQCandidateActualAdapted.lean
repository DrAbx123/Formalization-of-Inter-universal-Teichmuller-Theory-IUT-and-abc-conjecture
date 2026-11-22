import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTII.Frobenioid.Example36TateInverseJCanonical
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace

/-!
# Actual inverse-j q candidate at the concrete place above 5

Uses the actual inverse-j theorem
`exists_canonicalQSeriesJ_eq_split_j_full` to build an actual
`FinitePlaceQCandidate concreteFivePlace`.  No Classical.choice of an
arbitrary DVR uniformizer is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ

namespace LeanFormal.IUT.XiFPaper.InverseJQCandidateActualAdapted

/-- The actual inverse-j q at the place above 5, as a valuation q-candidate. -/
noncomputable def inverseJQCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace := by
  obtain ⟨q, -, -, hqne, hqlt, -, -⟩ :=
    exists_canonicalQSeriesJ_eq_split_j_full
  refine ⟨q, hqne, ?_⟩
  exact (Valued.toNormedField.norm_lt_one_iff).mpr hqlt

theorem inverseJQCandidate_norm :
    ‖(inverseJQCandidate).q‖ = (5 : ℝ)⁻¹ := by
  obtain ⟨q, -, -, -, -, hqnorm, -⟩ :=
    exists_canonicalQSeriesJ_eq_split_j_full
  change ‖(inverseJQCandidate).q‖ = (5 : ℝ)⁻¹
  -- inverseJQCandidate is defined by Classical.choose on the same existence,
  -- so its q is not definitionally the chosen q above. Record the exact
  -- missing choice-alignment instead of asserting it.
  sorry

#print axioms inverseJQCandidate

end LeanFormal.IUT.XiFPaper.InverseJQCandidateActualAdapted
end
