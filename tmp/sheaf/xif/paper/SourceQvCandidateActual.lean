import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment

/-!
# Actual q candidate from the closed source q_v theorem

For any finite place and split multiplicative curve, the closed source q_v
theorem gives an actual q parameter.  We turn it into a
`FinitePlaceQCandidate` without any arbitrary DVR choice.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.SourceQvClosed
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.SourceQvCandidateActual

universe u
variable {F : Type u} [Field F] [NumberField F]

local instance instAlgebraSourceField (v : NumberField.FinitePlace F) :
    Algebra F (NormalizedCompletion v) :=
  inferInstanceAs (Algebra F (Completion v))

local instance instAlgebraCompletionIntegers (v : NumberField.FinitePlace F) :
    Algebra (CompletionIntegers v) (NormalizedCompletion v) :=
  inferInstanceAs (Algebra (CompletionIntegers v) (Completion v))

local instance instIsFractionRingSourceLocalField (v : NumberField.FinitePlace F) :
    IsFractionRing (CompletionIntegers v) (NormalizedCompletion v) :=
  inferInstanceAs (IsFractionRing (CompletionIntegers v) (Completion v))

/-- The actual q parameter selected by the closed source q_v theorem. -/
noncomputable def sourceQvCandidate
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    NumberFieldFinitePlace.FinitePlaceQCandidate v := by
  let qv : SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic :=
    Classical.choice (exists_sourceQv_at_finitePlace_closed v X hsplit)
  refine ⟨qv.q, qv.q_ne_zero, ?_⟩
  exact (LeanFormal.IUT.SourceTateParameterAlignment.normalized_valued_lt_one_iff_norm_lt_one
    v qv.q).mpr qv.q_norm_lt_one

/-- The candidate's q is nonzero. -/
theorem sourceQvCandidate_q_ne_zero
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    (sourceQvCandidate v X hsplit).q ≠ 0 :=
  (sourceQvCandidate v X hsplit).q_ne_zero

#print axioms sourceQvCandidate

end LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
end
