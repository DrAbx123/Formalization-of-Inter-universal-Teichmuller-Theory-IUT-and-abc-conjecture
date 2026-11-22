import tmp.sheaf.xif.paper.S2697Gaussian2161Actual
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S2696VbadActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2699SourceQv2161Actual

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance instAlgebra2161 :
    Algebra GaussianField (NormalizedCompletion S2696GaussianPlace2161) :=
  inferInstanceAs (Algebra GaussianField (Completion S2696GaussianPlace2161))

/-- Actual source q_v at the Gaussian place above 2161, using the actual
split-multiplicative reduction S2697. -/
noncomputable def S2699SourceQv2161 :
    SourceQvClosed.SourceQv
      (K := NormalizedCompletion S2696GaussianPlace2161)
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace2161)).curve
      ((concreteSplitPuncturedCurve.baseChange GaussianField).baseChange
        (NormalizedCompletion S2696GaussianPlace2161)).isElliptic :=
  Classical.choice (SourceQvClosed.exists_sourceQv_at_finitePlace_closed
    S2696GaussianPlace2161 (concreteSplitPuncturedCurve.baseChange GaussianField)
    S2697Gaussian2161Actual.S2697_hasSplitMultiplicativeReductionAt2161)

/-- Its q value in the normalized completion. -/
def S2699Q : NormalizedCompletion S2696GaussianPlace2161 :=
  S2699SourceQv2161.q

theorem S2699Q_ne_zero : S2699Q ≠ 0 := S2699SourceQv2161.q_ne_zero
theorem S2699Q_norm_lt_one : ‖S2699Q‖ < 1 := S2699SourceQv2161.q_norm_lt_one

noncomputable def S2699Candidate :
    FinitePlaceQCandidate S2696GaussianPlace2161 := by
  have hcomp_norm : ‖(normalizedCompletionRingEquiv S2696GaussianPlace2161
      S2699Q : Completion S2696GaussianPlace2161)‖ < 1 :=
    (normalizedCompletion_norm_lt_one_iff S2696GaussianPlace2161 S2699Q).mpr
      S2699Q_norm_lt_one
  refine ⟨(normalizedCompletionRingEquiv S2696GaussianPlace2161 S2699Q :
      Completion S2696GaussianPlace2161), ?_, ?_⟩
  · exact fun h0 => S2699Q_ne_zero
      ((normalizedCompletionRingEquiv S2696GaussianPlace2161).injective (by simpa using h0))
  · exact (Valued.toNormedField.norm_lt_one_iff).mp hcomp_norm

theorem S2699Candidate_order_pos : 0 < S2699Candidate.order :=
  S2699Candidate.order_pos

#check S2699SourceQv2161
#check S2699Q
#check S2699Q_norm_lt_one
#check S2699Candidate
#check S2699Candidate_order_pos
#print axioms S2699Candidate_order_pos


theorem S2699_rationalPlace_residueNorm_eq_2161 :
    residueNormBase S2696Place2161 = 2161 := by
  unfold residueNormBase
  rw [S2696Place2161, NumberField.FinitePlace.maximalIdeal_mk]
  rw [S2696HeightOne2161_asIdeal_eq_span]
  rw [Ideal.absNorm_span_singleton]
  have h : Algebra.norm ℤ (2161 : ℤ) = 2161 := by simp
  have hnat : ((Algebra.norm ℤ (2161 : ℤ)).natAbs) = 2161 := by
    rw [h]
    norm_num
  exact_mod_cast hnat

theorem S2699_residueNorm_ge_2161 :
    2161 ≤ residueNormBase S2696GaussianPlace2161 := by
  rw [ArithmeticQPilotBaseChange.residueNormBase_eq_lower_pow
    (k := ℚ) S2696GaussianPlace2161]
  rw [S2696GaussianPlace2161_comap]
  rw [show residueNormBase S2696Place2161 = (2161 : ℝ) from
    by exact_mod_cast S2699_rationalPlace_residueNorm_eq_2161]
  have hf : 1 ≤ ArithmeticQPilotBaseChange.localResidueDegree
      (k := ℚ) S2696GaussianPlace2161 :=
    Nat.succ_le_of_lt (ArithmeticQPilotBaseChange.localResidueDegree_pos
      (k := ℚ) S2696GaussianPlace2161)
  calc
    (2161 : ℝ) = (2161 : ℝ) ^ 1 := by norm_num
    _ ≤ (2161 : ℝ) ^ ArithmeticQPilotBaseChange.localResidueDegree
        (k := ℚ) S2696GaussianPlace2161 := by
      exact pow_le_pow_right₀ (by norm_num) hf

theorem S2699_order_ge_one : 1 ≤ S2699Candidate.order :=
  Nat.succ_le_of_lt S2699Candidate_order_pos

theorem S2699_logMagnitude_ge_log2161 :
    Real.log 2161 ≤ localLogMagnitude S2699Candidate := by
  rw [localLogMagnitude_eq_order_mul_log]
  have hres : (2161 : ℝ) ≤ residueNormBase S2696GaussianPlace2161 := by
    exact_mod_cast S2699_residueNorm_ge_2161
  have hrespos : 0 < residueNormBase S2696GaussianPlace2161 :=
    lt_of_lt_of_le (by norm_num) hres
  have hlog : Real.log (2161 : ℝ) ≤ Real.log (residueNormBase S2696GaussianPlace2161) :=
    Real.log_le_log (by norm_num) hres
  have hord : (1 : ℝ) ≤ (S2699Candidate.order : ℝ) := by
    exact_mod_cast S2699_order_ge_one
  have hmul := mul_le_mul hord hlog (le_of_lt (Real.log_pos (by norm_num))) (by positivity)
  simpa [one_mul] using hmul

#check S2699_residueNorm_ge_2161
#check S2699_logMagnitude_ge_log2161
#print axioms S2699_residueNorm_ge_2161
#print axioms S2699_logMagnitude_ge_log2161

end LeanFormal.IUT.XiFPaper.S2699SourceQv2161Actual
end