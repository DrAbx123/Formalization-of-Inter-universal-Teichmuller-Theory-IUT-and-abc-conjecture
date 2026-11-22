import tmp.sheaf.xif.paper.S2697Gaussian2161Actual
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696VbadActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2700SourceQv2161OnlyActual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance instAlgebra2161 :
    Algebra GaussianField (NormalizedCompletion S2696GaussianPlace2161) :=
  inferInstanceAs (Algebra GaussianField (Completion S2696GaussianPlace2161))

noncomputable def S2700SourceQv2161 :
    SourceQvClosed.SourceQv
      (K := NormalizedCompletion S2696GaussianPlace2161)
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace2161)).curve
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace2161)).isElliptic :=
  Classical.choice (SourceQvClosed.exists_sourceQv_at_finitePlace_closed
    S2696GaussianPlace2161 (concreteSplitPuncturedCurve.baseChange GaussianField)
    S2697Gaussian2161Actual.S2697_hasSplitMultiplicativeReductionAt2161)

def S2700Q : NormalizedCompletion S2696GaussianPlace2161 := S2700SourceQv2161.q
theorem S2700Q_ne_zero : S2700Q ≠ 0 := S2700SourceQv2161.q_ne_zero
theorem S2700Q_norm_lt_one : ‖S2700Q‖ < 1 := S2700SourceQv2161.q_norm_lt_one

noncomputable def S2700Candidate :
    FinitePlaceQCandidate S2696GaussianPlace2161 := by
  have hcomp_norm : ‖(normalizedCompletionRingEquiv S2696GaussianPlace2161
      S2700Q : Completion S2696GaussianPlace2161)‖ < 1 :=
    (normalizedCompletion_norm_lt_one_iff S2696GaussianPlace2161 S2700Q).mpr
      S2700Q_norm_lt_one
  refine ⟨(normalizedCompletionRingEquiv S2696GaussianPlace2161 S2700Q :
      Completion S2696GaussianPlace2161), ?_, ?_⟩
  · exact fun h0 => S2700Q_ne_zero
      ((normalizedCompletionRingEquiv S2696GaussianPlace2161).injective (by simpa using h0))
  · exact (Valued.toNormedField.norm_lt_one_iff).mp hcomp_norm

theorem S2700Candidate_order_pos : 0 < S2700Candidate.order :=
  S2700Candidate.order_pos

#check S2700SourceQv2161
#check S2700Q
#check S2700Q_norm_lt_one
#check S2700Candidate
#check S2700Candidate_order_pos
#print axioms S2700Candidate_order_pos

end LeanFormal.IUT.XiFPaper.S2700SourceQv2161OnlyActual
end