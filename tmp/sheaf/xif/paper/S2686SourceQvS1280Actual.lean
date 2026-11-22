import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment
import LeanFormal.IUT.IUTII.Frobenioid.Example36TateUniformization

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.SourceQvClosed
open LeanFormal.IUT.SourceQvClosed.SourceQv
open LeanFormal.IUT.SourceTateParameterAlignment
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.TateUniformization
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2686SourceQvS1280Actual

/-- The actual source q_v at the concrete S1280 bad place above 5, from the
actual split-multiplicative reduction and the closed source q_v theorem. -/
noncomputable def S2686SourceQv :=
  Classical.choice (SourceQvClosed.exists_sourceQv_at_finitePlace_closed
    (concreteFivePlace) (concreteSplitPuncturedCurve)
    concreteSplitCurve_hasSplitMultiplicativeReductionAt_five)

/-- Its actual q value in the normalized completion. -/
def S2686Q : NormalizedCompletion concreteFivePlace := S2686SourceQv.q

theorem S2686Q_ne_zero : S2686Q ≠ 0 := S2686SourceQv.q_ne_zero

theorem S2686Q_norm_lt_one : ‖S2686Q‖ < 1 := S2686SourceQv.q_norm_lt_one

/-- The source q_v packaged as an actual FinitePlaceQCandidate. -/
noncomputable def S2686Candidate : FinitePlaceQCandidate concreteFivePlace := by
  have hcomp_norm : ‖(normalizedCompletionRingEquiv concreteFivePlace S2686Q :
      Completion concreteFivePlace)‖ < 1 :=
    (normalizedCompletion_norm_lt_one_iff concreteFivePlace S2686Q).mpr
      S2686Q_norm_lt_one
  refine ⟨(normalizedCompletionRingEquiv concreteFivePlace S2686Q :
      Completion concreteFivePlace), ?_, ?_⟩
  · exact fun h0 => S2686Q_ne_zero ((normalizedCompletionRingEquiv concreteFivePlace).injective (by simpa using h0))
  · exact (Valued.toNormedField.norm_lt_one_iff).mp hcomp_norm

theorem S2686Candidate_q : S2686Candidate.q = S2686Q := rfl

theorem S2686Candidate_order_pos : 0 < S2686Candidate.order :=
  S2686Candidate.order_pos

/-- Exact remaining arithmetic condition: the source q_v order is prime to l. -/
def S2686OrderCoprime (l : PrimeGeFive) : Prop :=
  Nat.Coprime S2686Candidate.order l.value

#check S2686SourceQv
#check S2686Q
#check S2686Q_norm_lt_one
#check S2686Candidate
#check S2686Candidate_order_pos
#check S2686OrderCoprime
#print axioms S2686Candidate_order_pos

end LeanFormal.IUT.XiFPaper.S2686SourceQvS1280Actual
end